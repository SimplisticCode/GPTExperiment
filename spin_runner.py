import os
import subprocess
from enum import Enum

class Outcome(Enum):
    COMPILATION_ERROR = 1
    VERIFICATION_ERROR = 2
    SUCCESS = 3

class SpinRunner:   
    @staticmethod
    def safely_delete_file(file_path):
        """
        Safely deletes the file at the given file path.
        
        Args:
        file_path (str): The file path to the file to delete.
        """
        if os.path.exists(file_path):
            os.remove(file_path)
    
    @staticmethod
    def remove_generated_files():
        """
        Removes the files generated by SPIN during model compilation.
        """
        # Remove the pan executable
        SpinRunner.safely_delete_file('pan')
        # Remove the pan.c/.b/.h/.p/.t/.m file
        SpinRunner.safely_delete_file('pan.c')
        SpinRunner.safely_delete_file('pan.b')
        SpinRunner.safely_delete_file('pan.h')
        SpinRunner.safely_delete_file('pan.p')
        SpinRunner.safely_delete_file('pan.t')
        SpinRunner.safely_delete_file('pan.m')
        # Remove the _spin_nvr.tmp file
        SpinRunner.safely_delete_file('_spin_nvr.tmp')
        
        # Remove the trail files
        trail_files = [f for f in os.listdir() if f.endswith('.trail')]
        for trail_file in trail_files:
            os.remove(trail_file)
        
    @staticmethod
    def compile_model(model_path):
        """
        Compiles the given model using SPIN to generate the pan executable.
        
        Args:
        model_path (str): The file path to the model.
        
        Returns:
        bool, str: A tuple containing a boolean indicating if the model was compiled successfully and a message.
        """
        
        # Ensure that the model file exists
        if not os.path.exists(model_path):
            raise FileNotFoundError(f"Model file not found: {model_path}")
        
        # Prepare the SPIN command
        compile_cmd = f"spin -a -DNOREDUCE {model_path}"
        gcc_cmd = "gcc -DNFAIR=3 -DNOREDUCE -o pan pan.c"
        
        try:
            # Run SPIN to generate the pan.c file
            compile_result = subprocess.run(compile_cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            # Check if the compilation was successful
            if compile_result.returncode != 0:            
                # Could not compile the model
                errorMessage = f"The following error occurred during model compilation. Stdout: {compile_result.stdout}, Stderr: {compile_result.stderr}"
                return (False, errorMessage)
            # Compile pan.c into the pan executable
            subprocess.run(gcc_cmd, shell=True, check=True)
            return (True, "Model compiled successfully.")
        except subprocess.CalledProcessError as e:
            print(f"An error occurred: {e}")
            return (False, f"An error occurred: {e}")
        
    @staticmethod
    def killMutants(mutants, specifications):
        """
        Eliminate all mutants that don't satisfy the LTL specifications.
        
        Args:
        mutants (list of str): The list of file paths to the mutants.
        specifications (list of str): The list of LTL specifications.
        
        Returns:
        list of str: The list of file paths to the surviving mutants.
        """
        surviving_mutants = []
        for mutant in mutants:
            result = SpinRunner.check_model(mutant, specifications)
            if result[0] == Outcome.SUCCESS:
                surviving_mutants.append(mutant)
            else:
                print(f"Mutant {mutant} eliminated. Reason: {result[0]}")
                # Remove the mutant file, the compiled files, the pan executable, and the trail files
        
        SpinRunner.remove_generated_files()    
        return surviving_mutants
        
    @staticmethod
    def check_model(file_name, formulas):
        """
        A function to check if the model satisfies the given LTL formulas.
        
        Args:
            file_name (str): The file path to the model.
            formulas (A dictionary of str: str): A dictionary containing the LTL formulas to check.
        
        Returns:
            (Outcome, str, dict, dict): A tuple containing an Outcome enum and a message.
        """
        satisfied_formulas = dict()
        could_compile, error_message = SpinRunner.compile_model(file_name)
        if not could_compile:
            # The model could not be compiled
            return (Outcome.COMPILATION_ERROR, error_message, satisfied_formulas, None)
        
        # Loop through the LTL formulas and check each one
        for ltl_formula in formulas:
            pan_cmd = f"./pan -a -f -N {ltl_formula}"
            print(f"Checking LTL formula: {ltl_formula} using the command: {pan_cmd}")
            try:
                result = subprocess.run(pan_cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
                if "errors: 0" in result.stdout:
                    satisfied_formulas[ltl_formula] = formulas[ltl_formula] if ltl_formula in formulas else None
                else:
                    failed_formula = {ltl_formula: formulas[ltl_formula] if ltl_formula in formulas else None}
                    error_message = f"Formula {ltl_formula} failed: {result.stdout}, error: {result.stderr}"
                    if satisfied_formulas != {}:
                        error_message = f"Model satisfies the following LTL formulas: {satisfied_formulas}, but failed on: {ltl_formula}. Error: {error_message}"
                    return (Outcome.VERIFICATION_ERROR, error_message, satisfied_formulas, failed_formula)
            except subprocess.CalledProcessError as e:
                return (Outcome.VERIFICATION_ERROR, f"An error occurred: {e} with the LTL formula: {ltl_formula}", satisfied_formulas, None)
        
        return (Outcome.SUCCESS, "Model satisfies all LTL formulas.", satisfied_formulas, None)
    