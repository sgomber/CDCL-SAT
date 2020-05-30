from SAT import SAT
import argparse
import sys

if __name__ == "__main__":
    
    # option whether to log while solving the
    # problem
    to_log = sys.argv[1]
    if to_log == "False":
        to_log = False
    elif to_log == "True":
        to_log = True
    else:
        raise ValueError("The first argument should be either True or False.")

    # Decision Heuristic to be used
    decider_to_use = sys.argv[2]
    
    # Restart Heuristic to be used
    # None if no restart strategy to be used
    restarter_to_use = sys.argv[3]

    # File name of the file containing
    # the input problem
    input_file_name = sys.argv[4]

    if restarter_to_use == "None":
        # If no restart strategy is to be used

        sat = SAT(to_log,decider_to_use)
        sat.solve(input_file_name)
        sat.stats.print_stats()
    else:
        # If a restart strategy is specified

        sat = SAT(to_log,decider_to_use,restarter_to_use)
        sat.solve(input_file_name)
        sat.stats.print_stats()



