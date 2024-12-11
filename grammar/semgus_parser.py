import json
import subprocess
import os

class SemGusParser:
    def __init__(self, exe_path=None, sem_file=None, json_output=None):
        """
        Initialize the parser with optional paths for conversion and parsing.
        """
        self.exe_path = exe_path
        self.sem_file = sem_file
        self.json_output = json_output
        self.grammar = {}
        self.semantic_rules = {}
        self.specification = []
        self.functions = {}
        self.synth_fun = {}

    def convert_sem_to_json(self):
        # Ensure output directory exists
        output_dir = os.path.dirname(self.json_output)
        if not os.path.exists(output_dir):
            os.makedirs(output_dir)
        
        # Construct the command to run semgus-parser.exe
        command = [
            self.exe_path,
            "--format", "json",
            "--mode", "batch",
            "--output", self.json_output,
            "--", self.sem_file
        ]
        
        try:
            # Run the command and capture output
            result = subprocess.run(command, capture_output=True, text=True, check=True)
            print("Conversion successful!")
        except subprocess.CalledProcessError as e:
            print(f"Error during conversion: {e}")
            print("Standard Output:", e.stdout)
            print("Standard Error:", e.stderr)

    def parse_json(self):
        """
        Parses the JSON file into abstract data structures (grammar, semantics, and specification).
        """
        if not self.json_output or not os.path.exists(self.json_output):
            raise FileNotFoundError(f"JSON file '{self.json_output}' does not exist.")

        with open(self.json_output, 'r') as f:
            semgus_data = json.load(f)

        for event in semgus_data:
            event_type = event.get("$event")
            
            # Grammar-related events
            if event_type in {"declare-term-type", "define-term-type"}:
                self._parse_term_type(event)
            elif event_type in {"define-function"}:
                self._parse_function(event)

            # Semantic rules
            elif event_type == "chc":
                self._parse_chc(event)

            # Specification
            elif event_type == "constraint":
                self._parse_constraint(event)

            elif event_type == "synth-fun":
                self._parse_synth_function(event)

            # Synthesis-related (still part of specification
            """"
            elif event_type == "synth-fun":
                self._parse_synth_function(event)
            elif event_type == "check-synth":
                self._handle_check_synth(event)
            elif event_type == "end-of-stream":
                self._handle_end_of_stream(event)
            """

    def _parse_term_type(self, event):
        """
        Parses term type declarations and definitions (grammar rules).
        """
        name = event.get("name")
        event_type = event.get("$event")
        if not name:
            print("Warning: Term type event is missing a 'name'.")
            return

        if event_type == "declare-term-type":
            # Handle term type declaration (if additional logic is required here)
            self.grammar.setdefault(name, {"constructors": []})

        elif event_type == "define-term-type":
            # Add constructors for a term type
            constructors = event.get("constructors", [])
            if name not in self.grammar:
                self.grammar[name] = {"constructors": constructors}
            else:
                self.grammar[name]["constructors"].extend(constructors)

    def _parse_function(self, event):
        """
        Parses function declarations and definitions and updates the grammar.
        Handles 'declare-function' and 'define-function' events.
        """
        name = event.get("name")
        rank = event.get("rank")  # Includes 'argumentSorts' and 'returnSort'
        definition = event.get("definition")
        types = rank["argumentSorts"]
        vars = definition["arguments"]

        self.functions[name] = dict(zip(vars, types))


    def _parse_chc(self, event):
        """
        Parses CHC (Constrained Horn Clauses) into the semantic rules.
        """
        chc_id = event.get("id")
        if not chc_id:
            print("Warning: CHC event is missing an 'id'.")
            return

        self.semantic_rules[chc_id] = {
            "head": event.get("head"),
            "bodyRelations": event.get("bodyRelations"),
            "inputVariables": event.get("inputVariables"),
            "outputVariables": event.get("outputVariables"),
            "variables": event.get("variables"),
            "constraint": event.get("constraint"),
            "constructor": event.get("constructor"),
            "symbols": event.get("symbols"),
        }

    def _parse_constraint(self, event):
        """
        Parses constraints into the specification.
        """
        constraint = event.get("constraint")
        if not constraint:
            print(f"Warning: Constraint event is missing a 'constraint': {event}")
            return
        self.specification.append(constraint)

    def _parse_synth_function(self, event):
        self.synth_fun = event

    def get_grammar(self):
        return self.grammar

    def get_semantics(self):
        return self.semantic_rules

    def get_specification(self):
        return self.specification

    def convert_and_parse(self):
        """
        End-to-end function: Converts .sem to .json and parses the JSON data.
        """
        self.convert_sem_to_json()
        self.parse_json()