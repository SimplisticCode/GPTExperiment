import datetime
from enum import Enum
import os
import textwrap
from openai import OpenAI

import logging

class PromptType(Enum):
    FIX_CompileError = 1
    FIX_VerificationError = 2
    CREATE_Specification = 3
    ENHANCE_Specification = 4

class Prompt:
    def __init__(self, 
                 prompt : str, 
                 promptType : PromptType,
                 promelaModel : str,
                 gptModel ="gpt-4o"):
        self.text = prompt
        self.promptType = promptType
        self.promelaModel = promelaModel
        self.gptModel = gptModel
        
        
class ChatGPTClient:
    def __init__(self, api_key, folder):
        self.api_key = api_key
        self.folder = folder
        self.client = OpenAI(
            # This is the default and can be omitted
            api_key=api_key
        )        
        # Step 1: Configure the logging
        log_file_path = os.path.join(self.folder, 'chatGPT.log')
        logging.basicConfig(filename=log_file_path, # Log file name
                    filemode='a',       # Append mode (use 'w' for overwrite)
                    format='%(asctime)s - %(levelname)s - %(message)s', # Include timestamp
                    datefmt='%Y-%m-%d %H:%M:%S', # Timestamp format
                    level=logging.INFO) # Log level
        
        
    def system_role(self, promptType : PromptType):
        promela_specific = textwrap.dedent("""
            An LTL formula is a formula in Linear Temporal Logic (LTL) that describes the behavior of a system over time.
            You can only refer to global variables in the LTL formula and not local variables defined within processes.
            Use temporal logic operators like 'U' (until), '<>' (eventually), and '[]' (always) to express properties, but try to avoid the 'X' operator.
            Avoid mentioning past values of variables and consider the default values of variables (ints are initialized to 0, bools to false).
            Also, avoid properties on channel variables.
        """)
                                            
        
        if promptType == PromptType.FIX_CompileError:
            system_role = textwrap.dedent("""
                                        You are a specialized assistant in computer science with deep expertise in the SPIN model checker, model checking and temporal logic.
                                        You are tasked with fixing a compilation error in a Promela model caused by an incorrect macro definition or ltl formula.
                                        You should use your expertise to identify the issue and correct it to ensure the model compiles successfully.
                                        First, analyze the error message to understand the cause of the compilation error before making the necessary changes.
                """) + promela_specific
            return system_role
        elif promptType == PromptType.FIX_VerificationError:
            system_role = textwrap.dedent("""
                                        You are a specialized assistant in computer science with deep expertise in the SPIN model checker, model checking and temporal logic.
                                        You are tasked with fixing a verification error in a Promela model caused by an ltl formula that does not capture the desired behavior.
                                        You should use your expertise to identify the issue and correct it to ensure the model verifies successfully.
                                        First, analyze the error message to understand the cause of the verification error before making the necessary changes.
                                        """) + promela_specific
            return system_role
        elif promptType == PromptType.CREATE_Specification:
            system_role = textwrap.dedent("""
                                        You are a specialized assistant in computer science with deep expertise in the SPIN model checker, model checking and temporal logic.
                                        You are tasked with creating an ltl formula that captures the desired behavior of a Promela model and distinguishes it from incorrect behaviors expressed by the provided mutants.
                                        You should use your expertise to analyze the model and mutants to define meaningful ltl properties that express the intended behavior.
                                        Start by analyzing the original model to understand its behavior and characteristics before defining ltl properties that capture its key features such as valid variable ranges, process interleaving, and state changes.
                                        For each mutant, identify the specific behavior that distinguishes it from the original model and create an ltl property that captures this distinction.
                                        The properties should be concise, clear, and written in valid Promela syntax to ensure accurate verification results.
                                        Finally, the ltl properties should be sorted such that the most general properties are checked first to eliminate mutants that violate them.
                                        """) + promela_specific
            return system_role
        elif promptType == PromptType.ENHANCE_Specification:
            system_role = textwrap.dedent("""
                                        You are a specialized assistant in computer science with deep expertise in the SPIN model checker, model checking and temporal logic.
                                        You are tasked with enhancing the existing LTL specifications for a Promela model to improve the verification results and eliminate more mutants.
                                        You should use your expertise to analyze the existing LTL properties and the mutants to identify areas for improvement and refinement.
                                        Start by reviewing the existing LTL properties to ensure they accurately capture the desired behavior of the model and distinguish it from incorrect behaviors expressed by the mutants.
                                        Identify any weaknesses or gaps in the existing properties that may allow mutants to pass verification and refine the properties to address these issues.
                                        You should not change the existing properties, but enhance them by adding new properties to cover the identified gaps and strengthen the verification process.
                                        """) + promela_specific
            return system_role
        else:
            # throw an exception
            raise ValueError("Invalid prompt type")
        
    def query_chatgpt(self, prompt : Prompt, seed: int = None, temperature: float = 0.2):
        """
        Queries ChatGPT with the given prompt and returns the response.

        Args:
        prompt (Prompt): The prompt to query ChatGPT with.

        Returns:
        str: The text response from ChatGPT.
        """
        # Save the prompt to a file
        name_of_model = os.path.basename(prompt.promelaModel)
        name_of_model = name_of_model.replace('.pml', '')
        
        system_role = self.system_role(prompt.promptType)
        
        dateTime = datetime.datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
        file_name = os.path.join(self.folder, f"prompt_{prompt.promptType.name}_{name_of_model}_{dateTime}.txt")
        with open(file_name, 'w') as f:
            f.write("The prompt to ChatGPT is:\n")
            f.write(system_role)
            f.write("\n")
            f.write(prompt.text)
        
        logging.info(f"Querying ChatGPT to {prompt.promptType.name} in the model {name_of_model}")
        try:
            completion = self.client.chat.completions.create(
                model=prompt.gptModel,
                messages=[
                    {
                    "role": "system",
                    "content": system_role
                    },
                    {"role": "user", "content": prompt.text}
                ],
                seed=seed,
                temperature=temperature,
            )
            response = completion.choices[0].message.content
            logging.info(f"Response from ChatGPT on {prompt.promptType.name} in the model {name_of_model}")
            # Append the response to the file
            with open(file_name, 'a') as f:
                f.write("The response from ChatGPT is:\n")
                f.write(response)
            
            return response
        except Exception as e:
            return str(e)
        
        