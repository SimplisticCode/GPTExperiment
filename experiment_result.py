import os

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
    