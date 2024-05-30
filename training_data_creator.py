

import os
import shutil
import subprocess
from deadulux_runner import DeaduluxRunner
from specification_generator import SpecificationGenerator
from response_parser import ResponseParser
from spin_runner import Outcome, SpinRunner


class TrainingData:
    model_file = ''
    specifications = []
    macros = []
    
    def __init__(self, model_file, specifications, macros):
        self.model_file = model_file
        self.specifications = specifications
        self.macros = macros

class TrainingDataGenerator:
    """
    This class is used to create training data for the GPT model.
    """
    base_models = []
    mutants = []
    
    def __init__(self, models):
        self.base_models = models
        self.mutants = []
        
    def check_model(self, model : TrainingData) -> bool:
        """
        A method to ensure that the promela model respects the specifications.
        
        Args:
        model (TrainingData): The model to check.
        
        Returns:
        bool: True if the model respects the specifications, False otherwise.
        """
        verdict, _, _, _ = SpinRunner.check_model(model.model_file, model.specifications)
        # Find pml.trail file and delete it
        counter_example = SpecificationGenerator.find_counter_example(model.model_file)
        if counter_example is not None and os.path.exists(counter_example):
            os.remove(counter_example)
            
        if verdict == Outcome.SUCCESS:
            return True
        else:
            return False
        
    def create_training_data(self, folder_name, chatGPTClient,  num_mutants=100):
        """
        A method to create the training data.
        """
        if not os.path.exists(folder_name):
            os.makedirs(folder_name)
            
        # Create folder for surviving mutants
        surviving_mutants_folder = os.path.join(folder_name, 'surviving_mutants')
        if not os.path.exists(surviving_mutants_folder):
            os.makedirs(surviving_mutants_folder)
            
        # Create folder for killed mutants
        killed_mutants_folder = os.path.join(folder_name, 'killed_mutants')
        if not os.path.exists(killed_mutants_folder):
            os.makedirs(killed_mutants_folder)
        
        for model in self.base_models:
            print(f"Processing model {model.model}")
            trace_files = DeaduluxRunner.generate_trace(model.model, 10, 100)
            # Generate specification for the model using ChatGPT
            updated_model = SpecificationGenerator.create_specification_model(model.model, folder_name, trace_files, chatGPTClient)
            
            # Read the updated model to get the macros and specifications
            with open(updated_model, 'r') as m:
                code = m.read()
                m.close()
                
            macros, specifications = ResponseParser.extract_macros_and_ltl_properties(code)
            
            code = SpecificationGenerator.remove_macros_and_specs(code)
            
            # copy the model to the folder
            model_file = os.path.join(folder_name, os.path.basename(model.model))
            with open(model_file, 'w') as f:
                f.write(code)
                f.close()
            
            mutants = DeaduluxRunner.generate_mutants(model_file, num_mutants)
            print(f"Generated {len(mutants)} mutants for model {updated_model}")
                      
            for mutant in mutants:
                # Add macros and specifications to the mutant
                updated_mutant = SpecificationGenerator.add_specification_to_model(folder_name, mutant, specifications, macros)
                mutant_data = TrainingData(updated_mutant, specifications, macros)
                survived = self.check_model(mutant_data)
                if survived:
                    print(f"Mutant {updated_mutant} survived.")
                    self.mutants.append(mutant_data)
                    # Move the mutant to the surviving mutants folder
                    shutil.move(updated_mutant, surviving_mutants_folder)
                else:
                    print(f"Mutant {updated_mutant} was killed.")
                    # Move the mutant to the killed mutants folder
                    shutil.move(updated_mutant, killed_mutants_folder) 
                    
            print(f"Finished processing model {model.model}")
                    
        print("Generated training data:")
        print(f"Number of surviving mutants: {len(self.mutants)}")
                    
        # Save the training data to a file
        with open('training_data.csv', 'w') as file:
            file.write("Model, Specifications, Macros\n")
            file.write("\n")
            for mutant in self.mutants:
                file.write(f"{mutant.model_file}\n")
                file.write(f"{mutant.specifications}\n")
                file.write(f"{mutant.macros}\n")
                file.write("\n")