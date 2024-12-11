import argparse
import os
from grammar.semgus_parser import SemGusParser
from solver.solver import SemGusSolver
#from src.solver import SemGusSolver

def main():

    print("Starting SemGus Solver...")

    parser = argparse.ArgumentParser(description="SemGus Constraint Solver")
    parser.add_argument("sem_file", help="Path to the input .sem file", default="input/example.sem")
    parser.add_argument("--json_output", help="Path to the intermediate JSON file", default="outputs/problem.json")
    parser.add_argument("--solution_output", help="Path to the solver's output", default="outputs/solution.json")
    parser.add_argument("--exe_path", help="Path to the semgus-parser.exe file", default="tools/semgus-parser.exe")
    args = parser.parse_args()
    
    # Convert .sem file to JSON using semgus-parser.exe
    #if not os.path.exists(args.json_output):
    print("Converting .sem to JSON...")
    parser = SemGusParser(args.exe_path, args.sem_file, args.json_output)
    parser.convert_sem_to_json()
    #else:
        #print("JSON file already exists, skipping conversion.")

    parser = SemGusParser(args.exe_path, args.sem_file, args.json_output)
    parser.parse_json()

    print("Hello")
    print(parser.grammar)
    #print(parser.specification)
    #for key, value in parser.semantic_rules.items():
    #    print(key + ": " + str(value))
    print("Goodbye")
    #print(parser.semantic_rules)
    #print(parser.specification)

    solver = SemGusSolver(
        grammar=parser.grammar,
        semantics=parser.semantic_rules,
        specification=parser.specification,
        functions=parser.functions,
        synth_fun=parser.synth_fun
    )
    solver.solve()

if __name__ == "__main__":
    main()