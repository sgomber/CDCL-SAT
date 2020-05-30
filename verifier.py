"""
Program to verify whether the assignment produces by the solver
satisfies the input problem file.
"""

import json
import sys

def check_validity(input_file_name,assgn_dict):
    """
    Method takes in a input file having a SAT problem and
    an assignment dictionary and checks whether the problem
    is satisfied by the assignment in the assignment dictionary.

    Parameters:
        input_file_name: Name of the input file storing the SAT problem
        assgn_dict: the dictionary storing the mapping of variables to the
        assigned boolean values

    Return:
        a boolean which is True if the passed assignment satisfies the
        SAT problem in the input file passed. It is False if the assignment
        is not a satisfying assignment
    """

    # Open the input file
    input_file = open(input_file_name,"r")
    
    # Value to be returned
    is_correct = True

    # For all lines in the file
    for line in input_file.readlines():
        # Remove trailing characters at the end of the line using rstrip
        line = line.rstrip()
        
        # Split the line with space as delimiter
        line = line.split()
        
        # First word of the line
        first_word = line[0]
        
        if first_word == "c" or first_word == "p":
            # If it is a comment or the line with number of vars
            # and clauses, ignore it
            continue
        else:

            # Satisfiability of this clause
            clause_sat = False

            # Remove the end 0 as in the DIMACS
            # CNF file
            clause = line[:-1]

            # For all literals in the clause
            for lit in clause:
                if lit[0] == "-":
                    # If the litteral is negative
                    var = lit[1:]

                    # Value read from the assignement
                    # dictionary is reversed
                    value = not assgn_dict[str(var)]
                else:
                    # Value is read from the assignment
                    # dictionary
                    value = assgn_dict[str(lit)]
                
                # OR is performed
                clause_sat = clause_sat or value
                
                # We break if the clause is already satisfied
                if clause_sat:
                    break
            
            # If the clause is not satisfied,
            # we set is_correct to False and
            # break (stop reading the file again
            # as we can now comment that assignment
            # is False) 
            if not clause_sat:
                is_correct = False
                break
    
    # Close the input file
    input_file.close()

    # Return the value
    return is_correct



if __name__ == "__main__":

    # Name of the file storing the input problem
    input_file_name = sys.argv[1]

    # Name of the file storing the variable assignments
    # produces by the solver
    assgn_file_name = sys.argv[2]

    # Open the assignment file
    assgn_file = open(assgn_file_name,"r")

    # Load the dictionary mapping the variables to the
    # boolean assignments using json.loads() method
    assgn_dict = json.loads(assgn_file.read())

    # Close the assignment file
    assgn_file.close()

    # Call the check_validity method to check if the input
    # file problem is satisfied by the assignment stored in
    # assgn_dict
    is_correct = check_validity(input_file_name,assgn_dict)
    
    # Print suitable messages based on if the assignment
    # is correct or not
    if is_correct:
        print("YES!! The assignment is valid.")
    else:
        print("NO!! The assignment is not valid.")