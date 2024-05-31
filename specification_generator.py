import os
import re
from ChatGptClient import ChatGPTClient
from experiment_result import ExperimentResult
from spin_runner import Outcome, SpinRunner
from query_builder import QueryBuilder
from response_parser import ResponseParser

class SpecificationGenerator:
    @staticmethod
    def find_counter_example(model):
        """
        Searches for the counter-example file for the given model.
        
        Args:
        model (str): The file path to the model.
        """
        file_name = os.path.basename(model)
        counter_example_file = file_name.replace('.pml', '.pml.trail')
        if os.path.exists(counter_example_file):
            return counter_example_file
        else:
            print(f"Counter-example file not found for the model: {model}")
            return None
    
    @staticmethod    
    def refine_model(model, specifications, add_examples : bool, chatGPTClient : ChatGPTClient):
        """
        Refines the given model by alternately checking the model with SPIN and enhancing the specifications using ChatGPT based on the feedback from SPIN.
        
        Args:
        model (str): The file path to the model.
        specifications (dict): The LTL specifications to refine.
        chatGPTClient (ChatGPTClient): The ChatGPT client to use for querying.
        
        Returns:
        str: The refined model with enhanced specifications.
        """
        # Run SPIN on the model to check the specifications and get feedback to enhance the specifications using ChatGPT
        # Loop until the model has no compilation or verification errors and satisfies all LTL formulas
        
        # Keep track of the previously failed specifications
        previously_failed_specs = dict()
        previously_satisfied_specs = dict()
        
        number_of_iterations = 0
        number_of_iterations_before_human_intervention = 1
        
        while True:
            if number_of_iterations >= number_of_iterations_before_human_intervention:
                print(f"The model {model} could not be corrected in {number_of_iterations_before_human_intervention} iterations.")
                print(f"Please check the model {model} and the specifications manually to see if you can identify the issue")
                print("You can also check the console output to see which LTL formulas are not satisfied.")
                # Wait for the user to check the model and specifications
                print("Press Enter to continue after checking the model and specifications.")
                input()
                model_content = ''
                with open(model, 'r') as file:
                    model_content = file.read()
                _, specifications = ResponseParser.extract_macros_and_ltl_properties(model_content)
                number_of_iterations = 0   
                
            print(f"Checking the model: {model} with SPIN.")
            verdict, message, satisfied_formulas, failed_formula = SpinRunner.check_model(model, specifications)
            dict.update(previously_satisfied_specs, satisfied_formulas)
            
            if verdict == Outcome.COMPILATION_ERROR:
                print(f"Compilation error - trying to fix the model {model} by querying ChatGPT with the error message from SPIN.")
                # Handle compilation errors using ChatGPT
                query = QueryBuilder.fix_compilation_query(model, message, add_examples)
                response = chatGPTClient.query_chatgpt(query)
                code = ResponseParser.extract_promela_code(response)
                
                # Extract the updated specification from the response
                _, specifications = ResponseParser.extract_macros_and_ltl_properties(code)
                # Save the response to the model file by overwriting the existing content
                with open(model, 'w') as file:
                    file.write(code)
            elif verdict == Outcome.VERIFICATION_ERROR:
                print(f"Verification error - trying to fix the model {model} by querying ChatGPT with the error message from SPIN.")
                # Keep track of the previously failed specifications
                dict.update(previously_failed_specs, failed_formula)
                # Handle verification errors
                counter_example_file = SpecificationGenerator.find_counter_example(model)
                with open(counter_example_file, 'r') as file:
                    counter_example = file.read()
                # Delete the counter-example file
                os.remove(counter_example_file)    
                # Query ChatGPT to fix the verification error
                query = QueryBuilder.fix_verification_query(model, message, counter_example, add_examples, previously_satisfied_specs, previously_failed_specs)
                response = chatGPTClient.query_chatgpt(query)
                code = ResponseParser.extract_promela_code(response)
                
                # Extract the updated specification from the response
                _, specifications = ResponseParser.extract_macros_and_ltl_properties(code)
                # Save the response to the model file by overwriting the existing content
                with open(model, 'w') as file:
                    file.write(code)
            elif verdict == Outcome.SUCCESS:
                # If the model satisfies all LTL formulas
                print(f"Success! The model {model} satisfies all LTL formulas.")
                break
            else:
                print("Unexpected outcome:", verdict)
                break
            number_of_iterations += 1
    
    @staticmethod
    def remove_macros_and_specs(model_content : str) -> str:
        """
        Removes macros (#define) and specifications (ltl) from a Promela file.

        Args:
        model_content (str): The content of the Promela file to remove macros and specifications from.

        Returns:
        Str: The content of the Promela file with macros and specifications removed.
        
        """
        # Regex pattern to match lines with #define or ltl
        pattern = re.compile(r"^\s*(#define|ltl)")

        # Split the content into lines
        lines = model_content.split('\n')

        # Filter lines that do not match the pattern
        cleaned_lines = [line for line in lines if not pattern.match(line)]

        # Join the cleaned lines
        cleaned_content = '\n'.join(cleaned_lines)
        return cleaned_content

    @staticmethod
    def add_specification_to_model(folder, model : str, specifications : dict, macros : dict, name_extension : str) -> str:
        """
        Add the given LTL specifications to the model file by creating a temporary file with the specifications.
        """
        # Ensure the model file exists
        if not os.path.exists(model):
            raise FileNotFoundError(f"Model file not found: {model}")
        
        file_name = os.path.basename(model)
        # Remove previous extensions from the file name
        file_name = file_name.replace('_specification', '')
        file_name = file_name.replace('_enhanced', '')
        # Also remove Iteration_1, Iteration_2, etc.
        file_name = re.sub(r'_Iteration_\d+', '', file_name)
        # Add the new extension
        file_name = file_name.replace('.pml', '_'+ name_extension + '.pml')
        file_name = os.path.join(folder, file_name)
        with open(file_name, 'w') as file:
            model_content = ''
            with open(model, 'r') as model_file:
                model_content = model_file.read()
            # Remove Specification from the model
            model_content = SpecificationGenerator.remove_macros_and_specs(model_content)
            for macro in macros:
                file.write(f'#define {macro} {macros[macro]}\n')
            for spec in specifications:
                ltl_formula = f'ltl {spec} {{ {specifications[spec]} }}'
                file.write(f'{ltl_formula}\n')
            with open(model, 'r') as model_file:
                file.write(model_content)
        return file_name
    
    @staticmethod
    def simplify_specifications(model : str, model_folder : str, mutants : list, experimentResult : ExperimentResult, chatGPTClient : ChatGPTClient):
        """
        Query ChatGPT to simplify the LTL specifications for the given model based on the surviving mutants.
        
        Args:
        model (str): The file path to the model.
        model_folder (str): The folder to store the model with the added LTL specification.
        mutants (list): The list of surviving mutants.
        chatGPTClient (ChatGPTClient): The ChatGPT client to use for querying.
        """
        
        query = QueryBuilder.simplify_formulas_query(model, experimentResult)
        response = chatGPTClient.query_chatgpt(query)
        macros, specifications = ResponseParser.parse_macros_and_specifications(response)
        updated_model = SpecificationGenerator.add_specification_to_model(model_folder, model, specifications, macros, 'simplified')
        
        add_examples = False

        SpecificationGenerator.refine_model(updated_model, specifications, add_examples, chatGPTClient)
        
        return updated_model

    
    @staticmethod
    def create_specification_model(model : str, model_folder : str, trace_files : list, add_examples : bool, chatGPTClient : ChatGPTClient) -> str:
        """
        Query ChatGPT to create a new LTL specification for the given model.
        
        Args:
        model (str): The file path to the model.
        model_folder (str): The folder to store the model with the added LTL specification.
        trace_files (list of str): The list of file paths to the traces.
        chatGPTClient (ChatGPTClient): The ChatGPT client to use for querying.
        
        Returns:
        str: The file path to the model with the added LTL specification.
        """
        
        query = QueryBuilder.create_specification_query(model, trace_files, add_examples)
        response = chatGPTClient.query_chatgpt(query)
        macros, specifications = ResponseParser.parse_macros_and_specifications(response)
        updated_model = SpecificationGenerator.add_specification_to_model(model_folder, model, specifications, macros, 'specification')

        SpecificationGenerator.refine_model(updated_model, specifications, add_examples, chatGPTClient)
        
        return updated_model
    
    
    @staticmethod
    def enhance_specification(model : str, model_folder : str, mutants : list, specifications : list, add_examples : bool, chatGPTClient : ChatGPTClient, name_extension: str) -> str:
        """
        Query ChatGPT to enhance the LTL specification for the given model based on the surviving mutants.
        
        Args:
        model (str): The file path to the model.
        model_folder (str): The folder to store the model with the added LTL specification.
        trace_files (list of str): The list of file paths to the traces.
        chatGPTClient (ChatGPTClient): The ChatGPT client to use for querying.
        
        Returns:
        str: The file path to the model with the added LTL specification.
        """
        
        query = QueryBuilder.enhance_specification_query(model, mutants, specifications)
        response = chatGPTClient.query_chatgpt(query)
        macros, specifications = ResponseParser.parse_macros_and_specifications(response)
        updated_model = SpecificationGenerator.add_specification_to_model(model_folder, model, specifications, macros, name_extension)

        SpecificationGenerator.refine_model(updated_model, specifications, add_examples, chatGPTClient)
        
        return updated_model