import argparse
import datetime
import os
import shutil
import textwrap
from ChatGptClient import ChatGPTClient
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

class SpecificationResult:
    def __init__(self, specification:str, surviving_mutants : list, killed_mutants: list):
        self.specification = specification
        self.surviving_mutants = surviving_mutants
        self.killed_mutants = killed_mutants
        self.num_killed_mutants = len(killed_mutants)
        self.num_surviving_mutants = len(surviving_mutants)
        self.mutation_score =  self.num_killed_mutants / ( self.num_killed_mutants + self.num_surviving_mutants)
        
class ExperimentResult:
    def __init__(self, model:str, iteration : int, killed_mutants: list, surviving_mutants: list, specificationDict: list):
        self.model = model
        self.iteration = iteration
        self.killed_mutants = killed_mutants
        self.surviving_mutants = surviving_mutants
        self.specificationDict = specificationDict    
        
    def __str__(self):
        num_killed_mutants = len(self.killed_mutants)
        num_surviving_mutants = len(self.surviving_mutants)
        result = f"Iteration: {self.iteration}\n"
        result += f"Model: {self.model}, Number of Killed Mutants: {num_killed_mutants}, Number of Surviving Mutants: {num_surviving_mutants}\n"
        for spec in self.specificationDict:
            killed_mutant_names = [os.path.basename(mutant) for mutant in spec.killed_mutants]
            result += f"Specification: {spec.specification}, Number of Killed Mutants: {spec.num_killed_mutants} - {killed_mutant_names} Mutation Score: {spec.mutation_score}\n"
        surviving_mutant_names = [os.path.basename(mutant) for mutant in self.surviving_mutants]
        result += f"Surviving Mutants: {surviving_mutant_names}\n"
        return result
    
    def log_iteration_to_file(self, file_name:str):
        print(f"Logging iteration results to file {file_name}")
        with open(file_name, 'a') as f:
            f.write(str(self))
            f.write('\n')
            f.close()
    
class Experiment:
    @staticmethod
    def check_model_all_specs(model_path : str, specifications):
        """
        A method to ensure that the promela model respects the specifications.
        
        Args:
        model (TrainingData): The model to check.
        specifications (Dict): The specifications to check against.
        
        Returns:
        bool: True if the model respects the specifications, False otherwise.
        """
        satisfiedFormulas = []
        dissatisfiedFormulas = []
        for spec in specifications:
            print(f"Checking model {model_path} against specification {spec}")
            specs = {}
            specs[spec] = specifications[spec]
            verdict, _, _, _ = SpinRunner.check_model(model_path, specs)
            if verdict == Outcome.SUCCESS:
                satisfiedFormulas.append(spec)
            else:
                dissatisfiedFormulas.append(spec)
                
        return satisfiedFormulas, dissatisfiedFormulas
    
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
    def check_all_mutants(folder_name:str, mutants: list, specifications: dict, macros: dict):
        killed_mutants, surviving_mutants = [], []
        specificationDict = {}
        for spec in specifications:
            specificationDict[spec] = []

        for mutant in mutants:
            # Add macros and specifications to the mutant
            updated_mutant = SpecificationGenerator.add_specification_to_model(folder_name, mutant, specifications, macros)
            _, dissatisfiedSpecs = Experiment.check_model_all_specs(updated_mutant, specifications)
            
            survived = len(dissatisfiedSpecs) == 0
            if survived:
                surviving_mutants.append(updated_mutant)
            else:
                Experiment.delete_counter_example(updated_mutant)
                killed_mutants.append(updated_mutant)
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
    def run_experiment(model:str, chatGPTClient: ChatGPTClient, folder_name:str, num_mutants:int, setup: ExperimentSetup):
        Experiment.create_folder_if_not_exists(folder_name)
        # Create folder for surviving mutants
        surviving_mutants_folder = Experiment.create_folder_if_not_exists(os.path.join(folder_name, 'surviving_mutants'))
        # Create folder for killed mutants
        killed_mutants_folder = Experiment.create_folder_if_not_exists(os.path.join(folder_name, 'killed_mutants'))
                
        print(f"Processing model {model}")
        trace_files = []
        if setup.traces_in_query:
            trace_files = DeaduluxRunner.generate_trace(model, 10, 100)
            
        mutants = DeaduluxRunner.generate_mutants(model, num_mutants)
            
        # Generate specification for the model using ChatGPT
        # Add option to include examples in the query
        updated_model = SpecificationGenerator.create_specification_model(model, folder_name, trace_files, chatGPTClient)
        
        # Delete trace files
        for trace_file in trace_files:
            os.remove(trace_file)
            
        # Read the updated model to get the macros and specifications
        with open(updated_model, 'r') as m:
            code = m.read()
            m.close()
                
        macros, specifications = ResponseParser.extract_macros_and_ltl_properties_file(updated_model)
        code = SpecificationGenerator.remove_macros_and_specs(code)
            
        # copy the model to the folder
        model_file = os.path.join(folder_name, os.path.basename(model))
        with open(model_file, 'w') as f:
            f.write(code)
            f.close()
            
        specificationDict = {}
        for spec in specifications:
            specificationDict[spec] = []
            
        model_name = os.path.basename(model).replace('.pml', '')
        result_file = os.path.join(folder_name, model_name + '_results.txt')
            
        experiments = []
        mutants_to_check = mutants
        # Check the model against the specifications
        for i in range(setup.number_iterations - 1):
            killed_mutants, surviving_mutants, specificationDict =  Experiment.check_all_mutants(folder_name, mutants_to_check, specifications, macros)                
            killed_mutants = Experiment.move_mutants_to_folders(killed_mutants, killed_mutants_folder)
            surviving_mutants = Experiment.move_mutants_to_folders(surviving_mutants, surviving_mutants_folder)

            # Log the iteration results to a file
            spec_results = []
            for spec in specificationDict:
                kMutants = specificationDict[spec]
                sMutants = []
                for mutant in mutants_to_check:
                    if mutant not in kMutants:
                        sMutants.append(mutant)
                spec_result = SpecificationResult(spec, sMutants, kMutants)
                spec_results.append(spec_result)
                specificationDict[spec] = []
            
            experiment_result = ExperimentResult(model, i + 1, killed_mutants, surviving_mutants, spec_results)
            experiment_result.log_iteration_to_file(result_file)
            experiments.append(experiment_result)
            
            if len(surviving_mutants) == 0:
                print(f"All mutants have been killed for model {model}")
                break
            
            # Enhance the specification
            print(f"Enhancing specification for model {model} as there are {len(surviving_mutants)} surviving mutants")
            specificationNames = list(specifications.keys())
            updated_model = SpecificationGenerator.enhance_specification(updated_model, folder_name, surviving_mutants, specificationNames, chatGPTClient)
            
            macros, specifications = ResponseParser.extract_macros_and_ltl_properties_file(updated_model)
            
            mutants_to_check = surviving_mutants

        # Run the final specification on all mutants
        Experiment.check_all_mutants(folder_name, mutants, specifications, macros)
            
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
    args = parser.parse_args()
    setup = ExperimentSetup(args.examples_in_query, args.mutants_in_query, args.api_key_chat_gpt, args.iterations)
    Experiment.run_experiments(setup, args.model_dir)

if __name__ == "__main__":
    main()
