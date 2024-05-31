import argparse
import datetime
import os
import shutil
from ChatGptClient import ChatGPTClient
from experiment_result import ExperimentResult, SpecificationResult
from spin_runner import Outcome, SpinRunner
from response_parser import ResponseParser
from specification_generator import SpecificationGenerator
from deadulux_runner import DeaduluxRunner

class ExperimentSetup:
    def __init__(self, 
                 examples_in_query : bool, 
                 mutants_in_query : bool, 
                 api_key_chat_gpt : str,
                 number_iterations : int = 1, 
                 traces_in_query : bool = True):
        self.examples_in_query = examples_in_query
        self.mutants_in_query = mutants_in_query
        self.api_key_chat_gpt = api_key_chat_gpt
        self.number_iterations = number_iterations
        self.traces_in_query = traces_in_query

class Experiment:   
    @staticmethod
    def create_folder_if_not_exists(folder_name:str) -> str:
        if not os.path.exists(folder_name):
            os.makedirs(folder_name)
        return folder_name    
    
    @staticmethod
    def delete_counter_example(model:str):
        trail_file_name = os.path.basename(model.replace('.pml', '.pml.trail'))
        file_path = os.path.realpath(__file__)
        trail_file = os.path.join(os.path.dirname(file_path), trail_file_name)
        if os.path.exists(trail_file):
            os.remove(trail_file)
    
    @staticmethod
    def check_all_mutants(folder_name:str, mutants: list, specifications: dict, macros: dict, name_extension:str):
        """
        Check all the mutants against the specifications and keep track of which mutants are killed and which are surviving of each specification.
        
        Args:
        folder_name (str): The folder where the mutants are stored.
        mutants (list of str): The list of mutants to check.
        specifications (dict): The specifications to check against.
        macros (dict): The macros in the model.
        
        Returns:
        list of str: The list of killed mutants.
        list of str: The list of surviving mutants.
        dict: The dictionary of mutants that are killed and surviving for each specification.
        """
        killed_mutants, surviving_mutants = [], []
        specificationDict = {}
        for spec in specifications:
            specificationDict[spec] = []

        for mutant in mutants:
            # Add macros and specifications to the mutant
            updated_mutant = SpecificationGenerator.add_specification_to_model(folder_name, mutant, specifications, macros, name_extension)
            _, dissatisfiedSpecs = SpinRunner.check_model_all_specs(updated_mutant, specifications)
            
            survived = len(dissatisfiedSpecs) == 0
            if survived:
                surviving_mutants.append(updated_mutant)
            else:
                Experiment.delete_counter_example(updated_mutant)
                killed_mutants.append(updated_mutant)
                for spec in dissatisfiedSpecs:
                    specificationDict[spec] = specificationDict[spec] + [mutant]
                
        return killed_mutants, surviving_mutants, specificationDict
    
    @staticmethod
    def move_mutants_to_folders(mutants : list, folder : str):
        new_mutants = []
        for mutant in mutants:
            shutil.move(mutant, folder)
            new_mutant = os.path.join(folder, os.path.basename(mutant))
            new_mutants.append(new_mutant)
        return new_mutants
    
    @staticmethod
    def create_experiment_result(model_file : str, iteration : int, mutants : list, specificationDict : dict) -> ExperimentResult:
        spec_results = []
        surviving_mutants, killed_mutants = set(), set()
        for spec in specificationDict:
            spec_killed_mutants = specificationDict[spec]
            killed_mutants = killed_mutants.union(set(spec_killed_mutants))
            spec_surviving_mutants = []
            for mutant in mutants:
                if mutant not in spec_killed_mutants:
                    spec_surviving_mutants.append(mutant)
            spec_result = SpecificationResult(spec, spec_surviving_mutants, spec_killed_mutants)
            spec_results.append(spec_result)
        surviving_mutants = set(mutants) - killed_mutants
        surviving_mutants = list(surviving_mutants)
        killed_mutants = list(killed_mutants)
        experiment_result = ExperimentResult(model_file, iteration, killed_mutants, surviving_mutants, spec_results)
        return experiment_result
    
    @staticmethod
    def run_experiment(model:str, chatGPTClient: ChatGPTClient, base_folder:str, num_mutants:int, setup: ExperimentSetup):
        model_name = os.path.basename(model).replace('.pml', '')
        folder_name = os.path.join(base_folder, model_name)
        
        Experiment.create_folder_if_not_exists(folder_name)
        # Create folder for surviving mutants
        surviving_mutants_folder = Experiment.create_folder_if_not_exists(os.path.join(folder_name, 'surviving_mutants'))
        # Create folder for killed mutants
        killed_mutants_folder = Experiment.create_folder_if_not_exists(os.path.join(folder_name, 'killed_mutants'))
                
        print(f"Processing model {model}")
        trace_files = []
        if setup.traces_in_query:
            trace_files = DeaduluxRunner.generate_trace(model, 10, 100)
            print(f"Generated {len(trace_files)} trace files")    
        
            
        mutants = DeaduluxRunner.generate_mutants(model, num_mutants)
            
        # Generate specification for the model using ChatGPT
        # Add option to include examples in the query
        updated_model = SpecificationGenerator.create_specification_model(model, folder_name, trace_files, setup.examples_in_query, chatGPTClient)
        
        # Delete trace files
        for trace_file in trace_files:
            os.remove(trace_file)
            
        # Read the updated model to get the macros and specifications
        with open(updated_model, 'r') as m:
            code = m.read()
            m.close()
        code = SpecificationGenerator.remove_macros_and_specs(code)
        # copy the model to the folder
        model_file = os.path.join(folder_name, os.path.basename(model))
        with open(model_file, 'w') as f:
            f.write(code)
            f.close()
                
        macros, specifications = ResponseParser.extract_macros_and_ltl_properties_file(updated_model)

        specificationDict = {}
        for spec in specifications:
            specificationDict[spec] = []
            
        model_name = os.path.basename(model).replace('.pml', '')
        result_file = os.path.join(folder_name, model_name + '_results.txt')
            
        experiments = []
        mutants_to_check = mutants
        # Check the model against the specifications
        for i in range(setup.number_iterations - 1):
            iteration_name = f"Iteration_{i + 1}"
            killed_mutants, surviving_mutants, specificationDict =  Experiment.check_all_mutants(folder_name, mutants_to_check, specifications, macros, iteration_name)                
            killed_mutants = Experiment.move_mutants_to_folders(killed_mutants, killed_mutants_folder)
            surviving_mutants = Experiment.move_mutants_to_folders(surviving_mutants, surviving_mutants_folder)

            # Log/Save the results
            experiment_result = Experiment.create_experiment_result(model, i + 1, mutants_to_check, specificationDict)
            experiment_result.log_iteration_to_file(result_file)
            experiments.append(experiment_result)
            
            for spec in specificationDict:
                specificationDict[spec] = []
            
            if len(surviving_mutants) == 0:
                print(f"All mutants have been killed for model {model}")
                break
            
            # Enhance the specification
            print(f"Enhancing specification for model {model} as there are {len(surviving_mutants)} surviving mutants")
            specificationNames = list(specifications.keys())
            updated_model = SpecificationGenerator.enhance_specification(updated_model, folder_name, surviving_mutants, specificationNames, setup.examples_in_query, chatGPTClient, iteration_name)
            
            macros, specifications = ResponseParser.extract_macros_and_ltl_properties_file(updated_model)
            
            mutants_to_check = surviving_mutants

        print(f"Checking the final specification for all mutants")
        macros, specifications = ResponseParser.extract_macros_and_ltl_properties_file(updated_model)

        # Run the final specification on all mutants
        killed_mutants, surviving_mutants, specificationDict = Experiment.check_all_mutants(folder_name, mutants, specifications, macros, 'final')
        experiment_result = Experiment.create_experiment_result(model, setup.number_iterations + 1, mutants, specificationDict)
        
        experiment_result.log_iteration_to_file(result_file)
        if len(surviving_mutants) > 0:
            print(f"Surviving mutants after all iterations: {surviving_mutants}")
        else:
            print(f"All mutants have been killed for model {model}")
            
        # Delete killed and surviving mutants
        for mutant in killed_mutants:
            os.remove(mutant)
        for mutant in surviving_mutants:
            os.remove(mutant)

        print(f"Trying to simplify the specification for the model {updated_model}")
        simplified_specifications = SpecificationGenerator.simplify_specifications(updated_model, folder_name, mutants, experiment_result, chatGPTClient)
        print(f"Simplified specifications: {simplified_specifications}")
            
        print(f"Finished processing model {model}")
        return experiments
    
    @staticmethod
    def run_experiments(experiment_setup : ExperimentSetup, models_dir: str):
        # Promela models in the directory
        models = [os.path.join(models_dir, f) for f in os.listdir(models_dir) if f.endswith('.pml')]
        
        # Create Result folder if it does not exist
        if not os.path.exists('Results'):
            os.makedirs('Results')
            
        # Create a folder to store Experiment results
        date = datetime.datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
        folder_name = 'Results/Evaluation-' + date
        os.makedirs(folder_name)
        
        prompt_folder = os.path.join(folder_name, 'prompt')
        # Create a folder to store the prompt
        os.makedirs(prompt_folder)

        chatGPTClient = ChatGPTClient(experiment_setup.api_key_chat_gpt, prompt_folder)
        
        results = []
        for model in models:
            result = Experiment.run_experiment(model, chatGPTClient, folder_name, 100, experiment_setup)
            results.append(result)
            
def main():
    parser = argparse.ArgumentParser(description="Specification Mining Experiments")
    parser.add_argument("-model_dir", help="The directory containing the Promela models to be used in the experiment.", type=str, default="Models/Experiment_2")
    parser.add_argument("-api_key", help="The API key for the ChatGPT model.", type=str, required=True)
    parser.add_argument("--examples_in_query", help="Include examples in the query to the GPT model.", action="store_true", default=True)
    parser.add_argument("--iterations", help="The number of iteration rounds for killing all mutants.", type=int, default=3)
    parser.add_argument("--mutants_in_query", help="Include mutants in the query to the GPT model.", action="store_true", default=False)
    parser.add_argument("--traces_in_query", help="Include traces in the query to the GPT model.", action="store_true", default=True)
    args = parser.parse_args()
    print(args)
    setup = ExperimentSetup(args.examples_in_query, args.mutants_in_query, args.api_key, args.iterations, args.traces_in_query)
    Experiment.run_experiments(setup, args.model_dir)

if __name__ == "__main__":
    main()
