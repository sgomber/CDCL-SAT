#!/usr/bin/env python
# coding: utf-8

# # SAT Solver implemented using CDCL Algorithm
# 
# SAT is the satisfiability problem wherein we are given some clauses containing propositional variables and the correspoding literals and we need to find whether the formula is satisfiable or unsatisfiable. A SAT Solver is a program that solves a SAT problem. Most of the state-of-the-art SAT solvers nowadays use the **CDCL (Conflict Driven Clause Learning)** algorithm to implement the solver.
# 
# ## CDCL Approach
# 
# To check whether the formula is SAT/UNSAT, the solver first picks a variable and assigns a boolean value to it. This is the **Decide** phase and is controlled by the decision heuristics used by the solver. Once the value is decided, the solver performs the **Boolean Constraint Propogation (BCP)** which is responsible for making implications after performing propogation once a variable is decided. Suppose we have a 3 literal clause (1,-2,3) and in the first 2 deciding steps, we set 1 as False and 2 as True. So, to make this clause true, we have to set 3 as true. This is basically what is intended by BCP. While the BCP makes implications, there can be 2 cases:
# 
# 1. It can reach a conflict. A conflict occurs if the BCP wants to set a variable v to the boolean value b but v has already been assigned !b (not b) either during decide phase or the BCP phase. Once this conflict occurs, the solver analyzes the conflict (**Analyze Conflict**) phase. 
#     1. If the conflict arises at level 0 (level 0 is the level where no decisions have been made and all the implications are the ones directly made using the input formula), it means that the given problem is UNSAT (unsatisfiable).  
#     2. If the conflict is not at level 0, then the solver comes out with a conflict clause. This clause is such that it has to be true or unless this conflict will occur again. So, this clause is added to the initial set of clauses which prevents this conflict to occur again in the future. Once the conflict clause is decided, it is used to find the level (in the decision tree) to which the solver should **Backtrack** (backjump). In backtracking, the solver undoes all the assignments and implications made at the levels greater than the backtrack level and reaches the backtrack level with the conflict clause added. It starts BCP again and this continues until either there are no conflicts and we reach case 2 or there is a conflict at level 0 and we reach case 1A.
# 
# 2. All the implications implied by the latest decision are made and the solver again goes to the Decide phase. If there are unassigned variables left, then the solver picks a variable and value to be assigned to it based on the heuristic and starts BCP. Else if there are no unassigned variables left, the problem is SAT (satisfiable) as all the variables have been assigned without any conflict.
# 
# Though the above algorithm is correct, but while solving some bigger problems, the solver can get stuck in a bad part and can spend redundant time there. If it would have taken another branch, the problem could have been solved earlier. To take care of this, we introduce **Restarts** in the solver. Restart heuristics analyze when has the solver stuck and makes the solver restart its computation. In restart, the solver undoes all the decisions and implications made on levels greater than equal to 1. The values used by the decision heuristic and the learned clauses are kept as is and these now lead to different set of variables being decided by the solver (as the decision heuristics and clause set is different now). Restarts have been found very effective and are used in all the state-of-the-art solvers.
# <hr style="border:2px solid gray"> </hr>
# The code below will implement this CDCL Algorithm. The details of the phases are explained below. The code initially has the import statements and helper classes.

# In[1]:


import os
import sys
import time
import json
import random
from collections import OrderedDict

# Import the Priority Queue class from PriorityQueue.py file
from PriorityQueue import PriorityQueue

# Import the Luby Sequence Generator methods from LubyGenerator.py file
from LubyGenerator import reset_luby, get_next_luby_number


# In[2]:


class Statistics:
    """
    Class used to store the various statistics measuerd while solving
    the SAT problem and defines method to print the statistics.
    
    Public Attributes:
        None
        
    Public Methods:
        print_stats(): Prints the statistics gathered during the solving of the SAT instance
    """
    
    def __init__(self):
        '''
        Constructor for the Statistics class.
        
        Arguments:
            None
        
        Return:
            intialized Statistics object
        '''    
        
        # Input file in which the problem is stored
        self._input_file = "" 
        
        # Result of the SAT solver (SAT or UNSAT)
        self._result = ""
        
        # Path of the output statistics file used to store
        # the statistics for the solved problem
        self._output_statistics_file = ""
        
        # Path of the output assignment file which stores the satisfying assignment
        # if the problem is satisfied, it is empty if the problem is UNSAT
        self._output_assignment_file = ""
        
        # Number of variables in the problem
        self._num_vars = 0
        
        # Original number of clauses present in the problem
        self._num_orig_clauses = 0
        
        # Number of original clauses stored
        # (The unary clauses are not stored and are directly used
        # to get the assignment)
        self._num_clauses = 0    
        
        # Number of clauses learned by the solver
        # during the conflict analysis
        self._num_learned_clauses = 0
        
        # Number of decisions made by the solver
        self._num_decisions = 0
        
        # Number of implications made by the 
        # solver (These are assignments which are
        # not decided but are implied from the decisions)
        self._num_implications = 0
        
        # Time at which the solver starts solving the problem
        self._start_time = 0
        
        # Time at which the solver is done reading the problem
        self._read_time = 0
        
        # Time at which the solver has completed solving the problem
        self._complete_time = 0
        
        # Time which the solver spend while performing BCP
        self._bcp_time = 0
        
        # Time which the solver spend while deciding (in _decide method)
        self._decide_time = 0
        
        # Time which the solver spend while analyzing the conflicts
        self._analyze_time = 0
        
        # Time which the solver spend while backtracking
        self._backtrack_time = 0
        
        # Number of restarts
        self._restarts = 0
    
    def print_stats(self):
        '''
        Method to print the statistics.
        
        Arguments:
            None
            
        Return:
            None
        '''
        
        # Print the stored statistics with appropriate labels of what the stats signify
        print("=========================== STATISTICS ===============================")
        print("Solving formula from file: ",self._input_file)
        print("Vars:{}, Clauses:{} Stored Clauses:{}".format(str(self._num_vars),str(self._num_orig_clauses),str(self._num_clauses)))
        print("Input Reading Time: ",self._read_time - self._start_time)
        print("-------------------------------")
        print("Restarts: ",self._restarts)
        print("Learned clauses: ",self._num_learned_clauses)
        print("Decisions made: ",self._num_decisions)
        print("Implications made: ",self._num_implications)
        print("Time taken: ",self._complete_time-self._start_time)
        print("----------- Time breakup ----------------------")
        print("BCP Time: ",self._bcp_time)
        print("Decide Time: ",self._decide_time)
        print("Conflict Analyze Time: ",self._analyze_time)
        print("Backtrack Time: ",self._backtrack_time)
        print("-------------------------------")
        print("RESULT: ",self._result)
        print("Statistics stored in file: ",self._output_statistics_file)
        
        # Check if the result of the problem is
        # SAT and if it is, then show the
        # assignement file name
        if self._result == "SAT":
            print("Satisfying Assignment stored in file: ",self._output_assignment_file)
        print("======================================================================")  


# In[3]:


class AssignedNode:
    """
    Class used to store the information about the variables being assigned.
    
    Public Attributes:
        var: variable that is assigned
        value: value assigned to the variable (True/False)
        level: level (decision level in the tree) at which the variable is assigned
        clause: The id of the clause which implies this decision (If this is assigned through implication) 
        index: The index in the assignment stack at which this node is pushed
    
    Public Methods:
        None
    """
    
    def __init__(self,var,value,level,clause): 
        '''
        Constructor for the AssignedNode class.
        
        Arguments:
            var: variable that is assigned
            value: value assigned to the variable (True/False)
            level: level (decision level in the tree) at which the variable is assigned
            clause: The id of the clause which implies this decision (If this is assigned through implication) 
            
        Return:
            initialized AssignedNode object
        '''
        
        # Variable that is assigned 
        self.var = var
        
        # Value assigned to the variable (True/False)
        self.value = value
        
        # Level at which the variable is assigned
        self.level = level   
        
        # The index of the clause which implies the variable var if var is assigned through Implication
        # If var is decided, this is set to None
        self.clause = clause 
        
        # Index at which a node is placed in the assignment stack
        # Initially it is -1 when node is created and has to be
        # updated when pushed in assignment_stack.
        self.index = -1
    
    def __str__(self):
        '''
        Method to get the string representation of the AssignedNode object.
        
        Parameters:
            None
        
        Return:
            a string that has the information about this node
        '''
        
        return_string = ""
        
        # Add variable info
        return_string += "Var: {} ".format(self.var)
        
        # Add value info
        return_string += "Val: {} ".format(self.value)
        
        # Add level info
        return_string += "Lev: {} ".format(self.level)
        
        # Add clause info
        return_string += "Cls: {} ".format(self.clause)
        
        # Add index info
        return_string += "Ind: {} ".format(self.index)
        
        # Return the final string
        return return_string


# # Input File Format
# 
# The input file is in the DIMACS CNF format. The problem in the DIMACS CNF format looks like this:
# 
# c A sample .cnf file. <br>
# p cnf 3 2 <br>
# 1 -3 0 <br>
# 2 3 -1 0 <br>
# 
# The lines starting with 'c' are the comments. The line starting with 'p' has the number of variables and the number of clauses after "cnf". Like, in the above example, there are 3 variables and 2 clauses. The next lines of the file are the clauses. Each clause ends with 0. In the input format, each variable is defined by a number. So, we have literals like 1, -2, 3 and so on. Let there be V number of variables. Positive literals are like 1,2,3,4...V and we store them like this only. For the negative literals, -1,-2,..-V, we will add V to its absolute value. That is, -1,-2,-3 ... -V will be represented by V+1,V+2..V+V. 
# 
# For eg. if we have 3 variables 1,2 and 3. Then the clause (1,-2,3) will be stored as (1,5,3) as -2 is replaced by 2+3=5
# <hr style="border:2px solid gray"> </hr>
# 
# # 2-Watched Literals to fasten BCP
# 
# Studies show that majority of the times, the SAT solver performs the Boolean Constraint Propogation (BCP) which is responsible for making implications after performing propogation once a variable is decided. A naive approach for doing so would be that whenever a variable is set, we traverse each clause and find such clauses where all but 1 literals have been falsed. This would be very expensive as we will have to traverse all the literals every time a decision is made. And as many decisions are made, BCP is indeed an important step and should be done faster.
# 
# To fasten the BCP, we observe that if for any clause, we have 2 literals that are not set false, then it can not pariticipate in BCP at this step. This is because as both the literals are not false, then either atleast one is true which means that the clause is already valid and can not be used to conclude anything or both are not set, which means that there are atleast two literals not defined and thus we can not say anything about the clause at this step. So, for all clauses, we keep 2 watch literals all the time with the invariant that each of them is not false if the clause is not satisfied. Now, whenever we set a variable, say 2 as in the above example and we set it to true. This means that the literal -2 (5) has been falsed and so we only go to clauses watched by -2 and search for a new watcher for them. If we get a new watcher for them, then it is fine. Else we are left with only one undecided literal in it (the other watcher) as we get no watcher (not false literal) which means all other literals have been falsed and so the only undecided literal left is the other watcher and that is now implied.
# <hr style="border:2px solid gray"> </hr>
# 
# # Decision Heuristics
# 
# The time which the solver takes to solve the problem can be reduced drastically by choosing the variable to be assigned and value that it should be assigned intelligently. This is done with the help of decision heuristics used by the SAT Solver. We implement the following three decision heuristics in this solver. 
# 
# 1. **ORDERED:** As seen above, the variables are represented as numbers 1,2,3 and so on. So, in this ordered decider, we pick the smallest (comparing the numbers representing the variables) unassigned variable and set it to True. To implement it, we traverse the list 1,2,3 .. V in this order and take the first variable which is unassigned and assign it True.
# 
# 2. **VSIDS:** In the VSIDS (Variable State Independent Decaying Sum) like strategy, we prefer the literals that recently participated in the conflict resolution and set them first. We create an array of size 2\*number of variables to store the scores of all literals and initialize it with all 0s. While reading the input file, the score of a literal is incremented by 1 whenever it appears in a clause. When ever a conflict occurs and a conflict cluase is created, we increase the score of all literals in that conflict clause by _incr (which is 1 initially) and _incr is increased by 0.75 after each conflict clause creation. This is done to give more weightage to the literals participating in the recent conflicts. While deciding, the unassigned literal with the highest score is chosen and is satisfied (if it is -v, v is set to False and if it is v, v is set to True)
# 
# 3. **MINISAT:** This is the heuristic as used by the MINISAT solver. It is on the lines of VSIDS with some modifications. Here, we maintain the score array for all variables (rather than the literals) and intialize the scores to 0. We also maintain a phase array which stores the last truth value assigned to each variable (whenever a variable is assigned, this phase array is updated). While reading the input file, the score of a variable is incremented by 1 whenever a literal corresponding to it appears in a clause. When ever a conflict occurs and a conflict cluase is created, we increase the score of all variables whose literals appear in that conflict clause by _incr (which is 1 initially) and _incr is divided by _decay (0.85) after each conflict clause creation. This is done to give more weightage to the variables participating in the recent conflicts. While deciding, the unassigned variable with the highest score is fixed. It is assigned the value it was assigned previously as stored in the phase array. This is called **phase-saving**. Phase-saving is beneficial as in a sense we are restarting the search for the solution of the problem by assigning the variable with the same value again. Conflicts that occured after this variable's assignment earlier lead to learning of conflict clauses which will now help in avoiding these conflict situations.
# 
# To implement the VSIDS and MINISAT heuristic, we implemented a PriorityQueue (in the file [PriorityQueue.py](PriorityQueue.py)) which has efficient methods to add a variable in the queue, increase the score of a variable in the queue, removing the variable from the queue (when assigned) and getting the variable with maximum score from the queue. All these are written efficiently taking O(log(n)) time. The working of the methods can be seen from the PriorityQueue.py which has been fully documented as well.
# <hr style="border:2px solid gray"> </hr>
# 
# 
# # Restart Heuristics
# 
# The restart heuristics mainly take the number of conflicts as the measure of the solver being stuck and restarts the solver when a certain number of conflicts have been reached. This limit is increased after each restart 
# Restart techniques used by the state-of-the-art solvers were studied and the following two of them were tried.
# 
# 1. **GEOMETRIC:** In this approach, we have a conflict limit and whenever the number of conflicts go beyond the limit, we restart the solver. Before restarting, the number of conflicts is set to 0 as we consider conflicts only after restart and the conflict limit is now increased by multiplying it with a constant (limit multiplier). This increasing of the conflict limit ensures the correctness as the solver sees if the problem can be solved in the fixed number of conflicts and if it is not solved, the limit is relaxed. This technique is named so because the conflict limits follow a **Geometric Series**. In our implementation, we initialize the conflict limit with 512 and keep the limit mulitplier as 2.
# 
# 2. **LUBY:** In this approach, the number of conflicts between 2 restarts are determined by the Luby Sequence. The Luby Sequence was given by Luby et. al. in 1993 and has been proven as an optimized startegy for randomized search algorithms. It has also proven to be very successful in SAT algorithms. The Luby sequence is given as:
# ![Images/luby.png](Images/luby.png)
# 
#     The Luby sequence thus looks like (1,1,2,1,1,2,4,1,1,2,1,1,2,4,8 ..). We have a base (512 in our implementation) and we multiply the base with the next luby number to get the conflict limit. So, the conflict limits in our implementation would vary like (512, 512, 1024, 512, 512, 1024, 2048 ...). Whenever the number of conflicts go beyond the limit, we restart the solver. Before restarting, the number of conflicts is set to 0 as we consider conflicts only after restart and the conflict limit is set to the next number in this list. This strategy tends towards more frequent restarts and completeness is guaranteed by the increasing upper limit on the number of conflicts. The Luby Sequence Generator has been implemented in the file [LubyGenerator.py](LubyGenerator.py) which is fully documented.
#     
# <hr style="border:2px solid gray"> </hr>
# 
# 
# The code below initializes the main SAT class and defines the various methods that the SAT class uses while solving the SAT problem.

# In[4]:


class SAT:
    """
    Class to store the data structures that are maintained while solving the SAT problem.
    It also stores the statistics of the solved problem and the methods that are used to solve the
    SAT problem.
    
    Public Attributes:
        stats: The statistics object that has the statistics of the solved SAT problem
    
    Public Methods:
        solve(filename): Takes as argument the filename which has the problem instance in the DIMACS CNF format 
        and solves it
    """
    
    def __init__(self,to_log,decider,restarter=None):
        '''
        Constructor for the SAT class
        
        Parameters:
            to_log: a boolean (True/False) which indicates whether the solver should log the progress while 
            solving the problem
            decider: the decision heuristic used while deciding the next variable to be assigned and the value
            to be assigned to it in the _decide method
            restarter: the restart strategy to be used by the SAT solver (None set by default, so if nothing is
            passed, restarting will not be used) 
        
        Return:
            initialized SAT object
        '''
        # Number of clauses stored
        self._num_clauses = 0 
        
        # Number of variables
        self._num_vars = 0   
        
        # Decision level (level at which the solver is in backtracking tree)
        self._level = 0
        
        # List of clauses where each clause is stored as a list of
        # literals as explained above.
        self._clauses = []
        
        # Dictionary mapping a literal to the list of clauses the literal watches
        self._clauses_watched_by_l = {}
        
        # Dictionary mapping a clause to the list of literals that watch the clause
        self._literals_watching_c = {}
        
        # Dictionary mapping the variables to their assignment nodes
        # which contains the information about the value of the variable,
        # the clause which implied the variable (if it is implied) and 
        # the level at which the variable is set
        self._variable_to_assignment_nodes = {}
        
        # A stack(list) that stores the assignment nodes in order
        # of their assignment
        self._assignment_stack = []
        
        # Boolean variable that stores whether the solver should
        # log progress information while solving the problem
        self._is_log = to_log
        
        # The decision heuristic to be used while solving
        # the SAT problem.
        # The decider must be ORDERED, VSIDS or MINISAT (discussed
        # above) (Raise error if it is not one of them)
        if decider not in ["ORDERED","VSIDS","MINISAT"]:
            raise ValueError('The decider must be one from the list ["ORDERED","VSIDS","MINISAT"]')
        self._decider = decider
        
        
        if restarter == None:
            # If no restart strategy passed,
            # set _restarter to None
            self._restarter = None
        else:
            
            if restarter not in ["GEOMETRIC","LUBY"]:
                # Check that the passed strategy should be
                # one of the GEOMETRIC or LUBY(as discussed above)
                # Raise error if it is not one of them
                raise ValueError('The restarter must be one from the list ["GEOMETRIC","LUBY"]')
            
            if restarter == "GEOMETRIC":
                # If the GEOMETRIC restart strategy is used,
                # then initialize the conflict limit with 512
                self._conflict_limit = 512
                
                # This is the limit multiplier by which the 
                # conflict limit will be multiplied after 
                # each restart
                self._limit_mult = 2
                
                # This stores the number of conflicts
                # before restart and is set to 0
                # at each restart
                self._conflicts_before_restart = 0
            
            if restarter == "LUBY":
                # If the LUBY restart strategy is used
                
                # Reset the luby sequencer to initialize it
                reset_luby()
                
                # We set base (b) as 512 here
                self._luby_base = 512
                
                # Intialize the conflict limit with
                # base * the first luby number fetched using the
                # get_next_luby_number()
                self._conflict_limit = self._luby_base * get_next_luby_number()
                
                # This stores the number of conflicts
                # before restart and is set to 0
                # at each restart
                self._conflicts_before_restart = 0
                
            
            # Set _restarter to the passed restart
            # strategy
            self._restarter = restarter
                
        
        # Statistics object used to store the statistics 
        # of the problem being solved
        self.stats = Statistics()


# In[5]:


def is_negative_literal(self,literal):
    '''
    Method that takes in number representation of a literal and 
    returns a boolean indicating if it represents a negative literal.
    
    Parameters:
        literal: The number representation of the literal
    
    Return:
        a Boolean which is True if the passed literal is False,
        else it is False
    '''
    
    # As discussed above, we add _num_vars to the absolute
    # value to get the representation for the negative literals.
    # So, we check if its value is greater than _num_vars to see
    # if it is negative.
    return literal > self._num_vars

# Add the method to the SAT class
SAT._is_negative_literal = is_negative_literal 


# In[6]:


def get_var_from_literal(self, literal):
    '''
    Method that takes in a literal and gives the variable corresponding to it.
    
    Parameters:
        literal: the literal whose corresponding variable is needed
    
    Return:
        the variable corrsponding to the passed literal
    '''
    
    # If the literal is negative, then _num_vars was added to 
    # the variable to get the literal, so variable can 
    # obtained by subtracting _num_vars from the literal
    if self._is_negative_literal(literal):
        return literal - self._num_vars
    
    # If the literal is positive, it is same as the variable
    # and so is returned as it is
    return literal

# Add the method to the SAT class
SAT._get_var_from_literal = get_var_from_literal


# In[7]:


def add_clause(self,clause):
    '''
    Method that takes in a clause, processes it and adds in to the 
    clause database for the problem.
    
    Parameters:
        clause: the clause (list of literals) to be added
        
    Return:
        None
    '''
    
    # Remove the 0 at the end of clause as in the DIMACS CNF format
    clause = clause[:-1]

    # OrderedDict's fromkeys method makes an 
    # dictionary from the elements of the list
    # clause and we again make a list from it
    # to remove dupicates.
    # (We could use set here but it does not maintain the order
    # and adds randomness)
    clause = list(OrderedDict.fromkeys(clause))
    
    # If it is a unary clause, then that unary literal
    # has to be set True and so we treat it as a special
    # case
    if len(clause)==1:
        # Get the literal
        lit = clause[0]
        
        # Value to be assigned to the variable
        # Set it to true initially
        value_to_set = True
        
        if lit[0]=='-':
            # If the literal is negative,
            # then the value of the variable should be 
            # set False, to satisfy the literal
            value_to_set = False
            var = int(lit[1:])
        else:
            # If the literal is positive, value_to_set remains True
            var = int(lit)
            
        
        if var not in self._variable_to_assignment_nodes:
            # If the variable has not been assigned yet
            
            # Increment the number of implications as it is an implication
            self.stats._num_implications += 1
            
            # Create an AssignmentNode with var, value_to_set, level 0
            # and clause None as we are not storing this clause
            node = AssignedNode(var,value_to_set,0,None)
            
            # Set the node with var in the dictionary and push it in the
            # assignment stack
            self._variable_to_assignment_nodes[var] = node
            self._assignment_stack.append(node)
            
            # Set the index of the node to the position in stack at which it
            # is pushed
            node.index = len(self._assignment_stack)-1
            
            # Log if _is_log is true
            if self._is_log:
                print("Implied(unary): ",node)
        else:
            # If the variable is assigned, get its node
            node = self._variable_to_assignment_nodes[var]
            
            # If the set value does not match with the value_to_set,
            # we have an contradiction and this has happened because of
            # two conflicting unary clauses in the problem. So, we decide
            # that the problem is UNSAT.
            if node.value != value_to_set:
                # Set the result in stats to UNSAT
                self.stats._result = "UNSAT"
                
                # Return 0 to indicate that the problem has been
                # solved. Proven UNSAT
                return 0
        
        # Everything normal
        return 1
        
    
    # This is the list of number representation of the literals
    clause_with_literals = []
    
    for lit in clause:
        if lit[0]=='-':
            # If literal is negative, then add _num_vars to
            # it to get the literal and push it to the list
            var = int(lit[1:]) # lit[1:] removes '-' at start
            clause_with_literals.append(var+self._num_vars)
            
            # If VSIDS decider is used, then increase the 
            # score of the literal appearing in the clause
            if self._decider == "VSIDS":
                self._lit_scores[var+self._num_vars] += 1
            
            # If MINISAT decider is used, then increase the
            # score of the variable corresonding to the
            # literal appearing in the clause
            if self._decider == "MINISAT":
                self._var_scores[var] += 1
        else:
            # If literal is positive, it is same as its variable 
            var = int(lit)
            clause_with_literals.append(var)
            
            # If VSIDS decider is used, then increase the 
            # score of the literal appearing in the clause
            if self._decider == "VSIDS":
                self._lit_scores[var] += 1
                
            # If MINISAT decider is used, then increase the
            # score of the variable corresonding to the
            # literal appearing in the clause
            if self._decider == "MINISAT":
                self._var_scores[var] += 1    
    
    # Set clause id to the number of clauses
    clause_id = self._num_clauses
    
    # Append the new clause to the clause list
    # and increase the clause counter
    self._clauses.append(clause_with_literals)
    self._num_clauses += 1
    
    # Make the first 2 literals as watch literals for this clause
    # (Maintains the invariant as both are not set and so are not false)
    watch_literal1 = clause_with_literals[0]
    watch_literal2 = clause_with_literals[1]
    
    # Set the watch literals for the clause to the list containing the 2 watchers
    self._literals_watching_c[clause_id] = [watch_literal1,watch_literal2]
    
    # (In python3, setdefault takes in a key and a value and if in the dictionary, that key has not
    # been assigned any value, the passed value is set)
    # Add this clause_id to the watched clauses list of both the watchers
    self._clauses_watched_by_l.setdefault(watch_literal1,[]).append(clause_id)
    self._clauses_watched_by_l.setdefault(watch_literal2,[]).append(clause_id)
    
    # Everything normal
    return 1
    
# Add the method to the SAT class
SAT._add_clause = add_clause


# In[8]:


def read_dimacs_cnf_file(self,cnf_filename):
    '''
    Method that takes in a filename of a file that has a SAT instance
    in the DIMACS CNF format and reads it to extract the clauses.
    
    Parameters:
        cnf_filename: The filename where the input (in DIMACS CNF format) is stored
        
    Return:
        None
    '''
    
    cnf_file = open(cnf_filename,"r")
    
    # For all lines in the file
    for line in cnf_file.readlines():
        # Remove trailing characters at the end of the line using rstrip
        line = line.rstrip()
        
        # Split the line with space as delimiter
        line = line.split()
        
        # First word of the line
        first_word = line[0]
        
        if first_word == "c":
            # If it is a comment, ignore it
            continue
        elif first_word == "p":
            # If it is the "p" line
            
            # Get the number of variables
            self._num_vars = int(line[2])
            
            # If VSIDS decider is used, then create the
            # _lit_scores array of size 2*_num_vars (for
            # all literals) and initialize the score of
            # all literals by 0
            if self._decider == "VSIDS":
                self._lit_scores = [0 for i in range(0,2*self._num_vars+1)]  
            
            # If MINISAT decider is used, then create the 
            # _var_scores array to store scores of all the
            # variables and initialize it to all zeroes.
            # Also, a _phase array is created which stores
            # the last assigned value of the variable
            # (O for false, 1 for true) (default initialized to 0)
            if self._decider == "MINISAT":
                self._var_scores = [0 for i in range(0,self._num_vars+1)]
                self._phase = [0 for i in range(0,self._num_vars+1)]
            
            # Store the original number of clauses (as given
            # by the last word of this line) in the stats object
            self.stats._num_orig_clauses = int(line[3])
        else:
            # If it is a clause, then call the _add_clause method
            ret = self._add_clause(line)  
            
            # If 0 is returned, then stop reading
            # as the problem is proved UNSAT
            if ret == 0:
                break
    
    # If the VSIDS decider is used
    if self._decider == "VSIDS":
        # Create a priority queue (max priority queue)
        # using the initialized scores
        self._priority_queue = PriorityQueue(self._lit_scores)
        
        # _incr is the quantity by which the scores of
        # a literal will be increased when it is 
        # found in a conflict clause
        self._incr = 1
        
        # Some variables may be already assigned because 
        # of being in the unary clauses, so remove both 
        # the literals corresponding to the variable
        for node in self._assignment_stack:
            self._priority_queue.remove(node.var)
            self._priority_queue.remove(node.var+self._num_vars)
    
    # If MINISAT decider is used
    if self._decider == "MINISAT":
        # Create a priority queue (max priority queue)
        # using the initialized scores
        self._priority_queue = PriorityQueue(self._var_scores)
        
        # _incr is the quantity by which the scores of
        # a variable will be increased when it is 
        # found in a conflict clause
        self._incr = 1
        
        # It is the value by which the previous 
        # scores will decay after each conflict
        self._decay = 0.85
        
        # Some variables may be already assigned because 
        # of being in the unary clauses, so remove them 
        # from the priority queue
        for node in self._assignment_stack:
            self._priority_queue.remove(node.var)
            
    # Close the input file
    cnf_file.close()

# Add the method to the SAT class
SAT._read_dimacs_cnf_file = read_dimacs_cnf_file


# In[9]:


def decide(self): 
    '''
    Method that chooses an uassigned variable and a boolean value for
    it and assigns the variable with that value
    
    Parameters:
        None
    
    Returns:
        -1 if there are no variables to set, else it returns the variable
        which is set
    '''
    
    # In these if else statements, we see what decider the solver is using
    # and then find the var and value_to_set
    
    if self._decider == "ORDERED":
        # If ORDERED decider is used, we start from 1 and get the smallest
        # unassigned variable and set it to True
        var = -1
        for x in range(1,self._num_vars+1):
            if x not in self._variable_to_assignment_nodes:
                var = x
                break

        value_to_set = True
        
    elif self._decider == "VSIDS":
        # If VSIDS decider is used, we get the literal with the highest
        # score from the priority queue
        literal = self._priority_queue.get_top()
        
        if literal == -1:
            # If it is -1, it means the queue is empty
            # which means all variables are assigned
            # and so we set var to -1
            var = -1
        else:
            # Get the variable associated to the literal
            var = self._get_var_from_literal(literal)
            
            # Store if the literal is negative
            is_neg_literal = self._is_negative_literal(literal)
            
            # We need to satisfy the literal so if it is 
            # negative, set the variable to False (which is
            # not True) and vice versa
            value_to_set = not is_neg_literal
            
            # Remove the lit complementary to
            # the above literal as we have fixed the
            # variable and so lit is no longer unassigned
            if is_neg_literal:
                self._priority_queue.remove(var)
            else:
                self._priority_queue.remove(var+self._num_vars)
                
    elif self._decider == "MINISAT":
        # If MINISAT decider is used, we get the variable with the
        # highest score from the priority queue
        var = self._priority_queue.get_top()
        
        # We use its last assigned value (as stored in the 
        # _phase array) to set it
        if var != -1:
            if self._phase[var] == 0:
                value_to_set = False
            else:
                value_to_set = True
    
    # If var is still -1, it means all the variables
    # are already assigned and so we return -1
    if var == -1:
        return -1
        
    # Increase the level by 1 as a decision is made
    self._level += 1
    
    # Create a new assignment node with var, value_to_set, level = _level
    # and clause None as this node is made through decide and not implication.
    # Add this node to the variable to node dictionary, append it to the stack
    # and set the index of the new node to the position at which it is pushed
    new_node = AssignedNode(var,value_to_set,self._level,None)
    self._variable_to_assignment_nodes[var] = new_node
    self._assignment_stack.append(new_node)
    new_node.index = len(self._assignment_stack)-1
    
    # Increase the number of decisions made in the stats object.
    self.stats._num_decisions += 1
    
    # Log if _is_log is true
    if self._is_log:
        print("Choosen decision: ",end="")
        print(new_node)
    
    # return the var which is set
    return var

# Add the method to the SAT class
SAT._decide = decide


# In[10]:


def boolean_constraint_propogation(self,is_first_time):
    '''
    Main method that makes all the implications. 
    
    There are two main cases. When it is run for the first time (if is_first_time is True), we can have many 
    decisions already made due to the implications by unary clauses and so we have to traverse through all and 
    make further implications. So, we start at the 0th index in the assignment list. If is_first_time is False, 
    it means that we only have to take the last made decision into account and make the implications and so we 
    start from the last node in the assignment stack.
    
    The implied decisions are pushed into the stack until no more implications can be made and "NO_CONFLICT"
    is returned, or a conflict is detected and in that case "CONFLICT" is returned. If the number of conflicts 
    reach a certain limit set by the restart heuristic, then the method returns "RESTART" and restarts the 
    solver.
    
    Parameters:
        is_first_time: Boolean which is set to True when this method is run initially and False for all
        other invocations
    
    Return:
        "CONFLICT" or "NO_CONFLICT" depending on whether a conflict arised while making the
        implications or not. Returns "RESTART" depending on the number of conflicts encountered
        and the restart strategy used by the solver (if any)
    '''
    
    # Point to the last decision
    last_assignment_pointer = len(self._assignment_stack)-1
    
    # If first time, then point to 0
    if is_first_time:
        last_assignment_pointer = 0
        
    # Traverse through all the assigned nodes in the stack 
    # and make implications
    while last_assignment_pointer < len(self._assignment_stack):
        # Get the assigned node
        last_assigned_node = self._assignment_stack[last_assignment_pointer]
        
        # If the variable's value was set to True, then negative literal corresponding to
        # the variable is falsed, else if it set False, the positive literal
        # is falsed
        if last_assigned_node.value == True:
            literal_that_is_falsed = last_assigned_node.var + self._num_vars
        else:
            literal_that_is_falsed = last_assigned_node.var
        
        # Now we change the watch literals for all clauses watched by literal_that_is_falsed
        
        itr = 0
        
        # Get the list of clauses watched by the falsed literal
        clauses_watched_by_falsed_literal = self._clauses_watched_by_l.setdefault(literal_that_is_falsed,[]).copy()
        
        # We iterate the list of clauses in reverse order as the conflict clauses
        # are to the end and we feel using them first is beneficial
        clauses_watched_by_falsed_literal.reverse()
        
        # Traverse through them and find a new watch literal and if we are unable to
        # find a new watch literal, we have an implication (because of the other watch literal)
        # If other watch literal is set to a value opposite of what is implied, we have a 
        # conflict
        while itr < len(clauses_watched_by_falsed_literal):
            # Get the clause and its watch list
            clause_id = clauses_watched_by_falsed_literal[itr]
            watch_list_of_clause = self._literals_watching_c[clause_id]
            
            # Get the other watch literal for this clause
            # (other than the falsed one)
            other_watch_literal = watch_list_of_clause[0]
            if other_watch_literal == literal_that_is_falsed:
                other_watch_literal = watch_list_of_clause[1]
            
            # Get the variable corresponding to the  watch literal
            # and see if the other watch literal is negative
            other_watch_var = self._get_var_from_literal(other_watch_literal)
            is_negative_other = self._is_negative_literal(other_watch_literal)
            
            # If other watch literal is set and is set so as to be true,
            # move to the next clause as this clause is already satisfied
            if other_watch_var in self._variable_to_assignment_nodes:
                value_assgned = self._variable_to_assignment_nodes[other_watch_var].value
                if (is_negative_other and value_assgned == False) or (not is_negative_other and value_assgned == True):
                    itr += 1
                    continue
            
            # We need to find a new literal to watch
            new_literal_to_watch = -1
            clause = self._clauses[clause_id]
            
            # Traverse through all literals
            for lit in clause:
                if lit not in watch_list_of_clause:
                    # Consider literals that are not watchers now
                    var_of_lit = self._get_var_from_literal(lit)
                    
                    if var_of_lit not in self._variable_to_assignment_nodes:
                        # If the literal is not set, it can be used as a watcher as it is
                        # not False
                        new_literal_to_watch = lit
                        break
                    else:
                        # If the literal's variable is set in such a way that the literal is
                        # true, we use it as new watcher as anyways the clause is satisfied
                        node = self._variable_to_assignment_nodes[var_of_lit]
                        is_negative = self._is_negative_literal(lit)
                        if (is_negative and node.value == False) or (not is_negative and node.value == True):
                            new_literal_to_watch = lit
                            break
            
            
            if new_literal_to_watch != -1:
                # If new_literal_to_watch is not -1, then it means that we have a new literal to watch the
                # clause
                
                # Remove the falsed literal and add the new literal to watcher list
                # of the clause
                self._literals_watching_c[clause_id].remove(literal_that_is_falsed)
                self._literals_watching_c[clause_id].append(new_literal_to_watch)
                
                # Remove clause from the watched clauses list of the falsed literal
                # and add it to the watched clauses list of the new literal
                self._clauses_watched_by_l.setdefault(literal_that_is_falsed,[]).remove(clause_id)
                self._clauses_watched_by_l.setdefault(new_literal_to_watch,[]).append(clause_id)
                
            else:
                if other_watch_var not in self._variable_to_assignment_nodes:
                    # We get no other watcher that means all the literals other than
                    # the other_watch_literal are false and the other_watch_literal
                    # has to be made true for this clause to be true. This is possible
                    # in this case as variable corresponding to the other_watch_literal
                    # is not set.
                    
                    # Get the value to set the variable as not of if the other watch literal
                    # is negative. If it is negative (is_negative_other is True), then its variable 
                    # should be set False (not True) and vice_versa
                    value_to_set = not is_negative_other
                    
                    # Create the AssignedNode with the variable, value_to_set, level and
                    # clause_id to refer the clause which is responsible to imply this.
                    # Then, store it in the variable to assignment dictionary with key
                    # other_watch_var.
                    assign_var_node = AssignedNode(other_watch_var,value_to_set,self._level,clause_id)
                    self._variable_to_assignment_nodes[other_watch_var] = assign_var_node
                    
                    # Push the created node in the assignment stack and set its 
                    # index to the position at which it is pushed.
                    self._assignment_stack.append(assign_var_node)
                    assign_var_node.index = len(self._assignment_stack)-1
                    
                    # If the VSIDS decider is used, then remove the
                    # two literals corresponding to the variable implied
                    # above as we maintain only the unassigned variables in
                    # the priority queue
                    if self._decider == "VSIDS":
                        self._priority_queue.remove(other_watch_var)
                        self._priority_queue.remove(other_watch_var+self._num_vars)
                    
                    # If MINISAT decider is used
                    if self._decider == "MINISAT":
                        # Remove the variable which is now set from 
                        # the priority queue as we only maintain
                        # the unassigned varibles in the priority
                        # queue
                        self._priority_queue.remove(other_watch_var)
                        
                        # Use the value_to_set to set the phase 
                        # of the variable
                        if value_to_set == False:
                            self._phase[other_watch_var] = 0
                        else:
                            self._phase[other_watch_var] = 1
                        
                    # Increment the number of implications in the stats 
                    # object by 1
                    self.stats._num_implications += 1
                    
                    # Log if _is_log is True
                    if self._is_log:
                        print("Implied decision:", end="")
                        print(assign_var_node)
                else:
                    
                    if self._restarter == "GEOMETRIC":
                        # If the GEOMETRIC restart strategy is used
                        
                        # Increase the conflicts_before_restart by 1
                        # as we have encountered a conflict
                        self._conflicts_before_restart += 1
                        
                        
                        if self._conflicts_before_restart >= self._conflict_limit:
                            # If the number of conflicts reach (or cross) the limit
                            # we RESTERT
                            
                            # Increment the restart counter in the stats object
                            self.stats._restarts += 1
                            
                            # Set the conflicts before restart to 0 
                            # as now it will be used to count the 
                            # new conflicts after the restart
                            self._conflicts_before_restart = 0
                            
                            # As in GEOMETRIC restart strategy,
                            # multiply the conflict limit by the
                            # pre defined limit multiplier
                            self._conflict_limit *= self._limit_mult
                            
                            # Log if _is_log is true
                            if self._is_log:
                                print("RESTARTING with GEOMETRIC RESTART LIMIT {}".format(self._conflict_limit))
                            
                            # return "RESTART" indicating that the solver needs to restart
                            return "RESTART"
                        
                    if self._restarter == "LUBY":
                        # If the LUBY restart strategy is used


                        # Increase the conflicts_before_restart by 1
                        # as we have encountered a conflict
                        self._conflicts_before_restart += 1

                        if self._conflicts_before_restart >= self._conflict_limit:
                            # If the number of conflicts reach (or cross) the limit
                            # we RESTERT

                            # Increment the restart counter in the stats object
                            self.stats._restarts += 1


                            # Set the conflicts before restart to 0 
                            # as now it will be used to count the 
                            # new conflicts after the restart
                            self._conflicts_before_restart = 0

                            # As in LUBY restart strategy,
                            # multiply the base by the next 
                            # luby number
                            self._conflict_limit = self._luby_base * get_next_luby_number()

                            # Log if _is_log is true
                            if self._is_log:
                                print("RESTARTING with LUBY RESTART LIMIT {}".format(self._conflict_limit))

                            # return "RESTART" indicating that the solver needs to restart
                            return "RESTART"
                        
                    # Conflict is detected as the other_watch_literal is not unassigned (as it is in this
                    # else case) and it is not true (as if it was true as we checked this earlier)
                    
                    # Create a conflict node and push it to assignment stack. (Var and Value are set None
                    # and the level and clause is set to the current level and the present clause that 
                    # caused the conflict). Conflict node is needed to store which clause caused the conflict 
                    # and the level at which the conflict occured
                    conflict_node = AssignedNode(None,None,self._level,clause_id)
                    self._assignment_stack.append(conflict_node)
                    
                    # Set its index to the position at which it is pushed
                    conflict_node.index = len(self._assignment_stack)-1
                    
                    # Log if _is_log is True
                    if self._is_log:
                        print("CONFLICT")
                    
                    # Return "CONFLICT" as a conflict is encountered
                    return "CONFLICT"
            
            # Increment itr to get the next clause
            itr += 1
        
        # Increment last_assignment_pointer to get the next assigned node
        # to be used to make the implications
        last_assignment_pointer += 1
    
    # If the loop finishes successfully, it means all the 
    # implications have been made without any conflict
    # and "NO_CONFLICT" is returned
    return "NO_CONFLICT"

# Add the method to the SAT class
SAT._boolean_constraint_propogation = boolean_constraint_propogation


# # Analyzing Conflict and Backjumping
# 
# We are implementing the CDCL (Conflict Driven Clause Learning) approach to solve the SAT problem. In this, whenever we have a conflict, we derive a conflict clause and add it to our clause database. Adding this clause will help the solver ignore this conflict path in the future.
# 
# If we create the Implication Graph, then a conflict clause can be thought of as a cut in the graph. A conflict clause has the sufficient literals such that if all are false together, then the same conflict will rise again and so this conflict clause should be true and thus is added to the clause database. But, there can be many potential conflict clauses.
# 
# ## BackJumping
# 
# In normal backtracking approach, whenever we reach a conflict, we backtrack one level and reverse that decision and try again. But, in the CDCL approach, we use the concept of backjump where we jump to a higher level which is decided by the conflict clause. Say the conflict occured at Level L. For all the literals in our conflict clause, we will take the levels at which they were set and find the maximum level less than L. Let's call this $L_{Backjump}$. We will then jump to $L_{Backjump}$ and undo all the decisions and implications that were made at levels greater than $L_{Backjump}$. 
# <hr style="border:2px solid gray"> </hr>
# 
# ## Choosing the right Conflict Clause
# 
# Let the level where conflict arised be L. We will choose a conflict clause that will have only one literal (say l) set at the level L. If this is the case, then as seen above, when we jump back using this clause, only this literal l will not be set and all other literals will be false and so we will have a new implication of l at that level which can then lead to further new implications.
# 
# This one literal l, set at the conflict level L will be chosen as the **first Unique Implication Point (UIP)**. A UIP in a implication graph is a node that occurs on all paths from the decision node at that level to the conflict node. First UIP is the UIP closest to the conflict node.
# 
# To find the conflict clause with only one node set at level L and that too, the first UIP, we use the following algorithm:
# 
# 1. Start with the clause C set as the clause that caused the conflict.
# 2. Find out the latest assigned (implied) variable (say V) in C.
# 3. Let the clause that caused the implication of V be C1.
# 4. Set C to the binary resolution of C and C1 with respect to the variable V.
#    Binary resolution of Clause1 = (p1,p2,p3,...pn,a) and Clause2 = (q1,q2,q3,...qn,-a) with respect to the variable a is the clause (p1,p2,p3,...pn,q1,q2,q3,...qn)
# 5. If C is such that it has only one literal set at L, then this is the final conflict clause. Else the steps
#    2-4 are repeated until the final conflict clause (with only one literal set at the conflict level L which also corresponds to the first UIP) is obtained.
# 
# This clause is then added to the clause database and the SAT solver jumps to the level $L_{Backjump}$ as described in the previous section.
# <hr style="border:2px solid gray"> </hr>
# 
# The methods implemented below are the ones related to analyzing the conflicts and backtracking.

# In[11]:


def binary_resolute(self,clause1,clause2,var):
    '''
    Method that takes in two clauses, clause1 and clause2 and performs
    their binary resolution (as described above) with respect to the passed
    variable.
    
    Parameters:
        clause1: the first clause(list of literals)
        clause2: the second clause(list of literals)
        var: the variable with respect to which the binary resolution should be performed
    
    Return:
        the binary resolution of the passed clauses (Clause 1 and Clause 2) with respect to
        the passed variable (var)
    '''
    
    # Add the clause 2 list of literals ahead of clause 1
    full_clause = clause1 + clause2
    
    # We made sure that the clauses have no duplicates but
    # after merging two clauses, we can have duplicates so we
    # remove them
    full_clause = list(OrderedDict.fromkeys(full_clause))
    
    # As in the defination of binary resolution, we
    # remove the positive literal (var) and the negative
    # literal (var+self._num_vars) from the combined list to
    # get the final resolution clause
    full_clause.remove(var)
    full_clause.remove(var+self._num_vars)
    
    # return the final clause
    return full_clause 

# Add the method to the SAT class
SAT._binary_resolute = binary_resolute


# In[12]:


def is_valid_clause(self,clause,level):
    '''
    Method that checks if the passed clause is a valid conflict clause (
    with only one literal set at level). This method while traversing the clause
    also finds the latest assigned literal set at level
    
    Parameters:
        clause: the clause that has to be checked
        level: the level at which the conflict occurs
    
    Return:
        a boolean which is True if the passed clause is a valid conflict clause
        the latest assigned literal set at level
    '''
    
    # To count the literals set at level
    counter = 0
    
    # Store the maximum index of the literals encountered
    maxi = -1
    
    # Candidate literal that is assigned the latest at level
    cand = -1
    
    for lit in clause:
        # For all literals in the clause,
        # get the assignment node corresponding
        # the variable of the literal
        var = self._get_var_from_literal(lit)
        node = self._variable_to_assignment_nodes[var]
        

        if node.level == level:
            # If the level at which the node is assigned
            # is same as the passed level
            
            # Increase the counter of literals assigned
            # at passed level by 1
            counter += 1
            
            # We need to find the latest assigned node at this 
            # level. latest assigned means the greatest index
            # value.
            if node.index > maxi:
                # If the node's index value is greater than maxi,
                # set maxi to the node's index and set the candidate
                # as the node
                maxi = node.index
                cand = node
                
    # Conflict is valid if counter == 1, so return counter == 1
    # and the candidate node (latest assigned node at the passed level)
    return counter == 1,cand

# Add the method to the SAT class
SAT._is_valid_clause = is_valid_clause


# In[13]:


def get_backtrack_level(self,conflict_clause,conflict_level):
    '''
    Method to get the backtrack level (level to which the solver should jump)
    using the passed conflict clause and the conflict level. The method also
    returns the only literal assigned at the conflict level present in the 
    conflict clause.
    
    Parameters:
        conflict_clause: the passed conflict clause
        conflict_level: the passed conflict level
        
    Return:
        the level to which the solver should backtrack and
        the only literal assigned at the conflict_level in the conflict_clause
    '''
    
    # Stores the backtrack level
    maximum_level_before_conflict_level = -1
    
    # Stores the only literal in the conflict
    # clause which is assigned at the conflict level
    literal_at_conflict_level = -1
    
    
    for lit in conflict_clause:
        # For all literals in the clause,
        # get the assignment node corresponding
        # the variable of the literal
        var = self._get_var_from_literal(lit)
        assigned_node = self._variable_to_assignment_nodes[var]
        
        
        if assigned_node.level == conflict_level:
            # If the node's level is the conflict_level,
            # set this lit to literal_At_conflict_level
            literal_at_conflict_level = lit
        else:
            # Else, we need to find the maximum of all the levels
            # other than the conflict level. If this node's level 
            # is greater than the maximum seen till now, the maximum 
            # is set to this node's level
            if assigned_node.level > maximum_level_before_conflict_level:
                maximum_level_before_conflict_level = assigned_node.level
    
    # Return the backtrack level and the literal at conflict level
    return maximum_level_before_conflict_level, literal_at_conflict_level

# Add the method to the SAT class
SAT._get_backtrack_level = get_backtrack_level


# In[14]:


def analyze_conflict(self):
    '''
    Method that is called when a conflict occurs during the 
    Boolean Constrain Propogation (BCP). It analyzes the conflict,
    generates the valid conflict clause (as discussed above) and adds
    it to the clause database. It then returns the backtrack level
    and the assignment node implied by the conflict clause that will be used 
    for implications once the solver backtracks (described below in the algorithm).
    
    Parameters:
        None
        
    Return:
        the level to which the solver should jump back and
        the assignement node implied by the conflict clause    
    '''
    
    
    # As this method is called, it means there was a conflict and
    # the last node in the assignment stack is a conflict node
    assigment_stack_pointer = len(self._assignment_stack)-1
    
    # The conflict node is used to get the conflict level and the
    # clause that caused the conflict
    conflict_node = self._assignment_stack[assigment_stack_pointer]
    conflict_level = conflict_node.level
    conflict_clause = self._clauses[conflict_node.clause]
    
    # As we are analyzing the conflict, we can remove it 
    # from the assignment stack
    self._assignment_stack.pop()
    
   # Log the conflict node if _is_log is True
    if self._is_log:
        print("Analyzing Conflict in the node: ",end="")
        print(conflict_node)
    
    # If the conflict is at level 0, then the problem is
    # UNSAT as till now, no decisions have been made and
    # we have reached a conflict. So we return -1 as the backtrack level
    # and None as the new implied node to represent UNSAT
    if conflict_level == 0:
        return -1,None
    
    # The loop responsible for finding the conflict clause
    while True:
        # is_nice tells whether the conflict clause has only one literal set
        # at the conflict level and prev_assigned_node is the latest assigned literal
        # on the conflict level present in the conflict clause
        is_nice,prev_assigned_node = self._is_valid_clause(conflict_clause,conflict_level)
        
        # If the clause is nice, i.e., it is the
        # final conflict clause, then break
        if is_nice:
            break
        
        # Log if _is_log is true
        if self._is_log:
            print("Clause: ",conflict_clause)
            print("Node_to_use ",prev_assigned_node)
            
        # If the conflict clause is not the final clause, then
        # as decribed above, replace it with its binary resolution
        # with the clause corresponding to the latest assigned literal
        clause = self._clauses[prev_assigned_node.clause]
        var = prev_assigned_node.var
        conflict_clause = self._binary_resolute(conflict_clause,clause,var)
    
    # Log if _is_log is true
    if self._is_log:
        print("Conflict Clause: ",conflict_clause)
            
    if len(conflict_clause) > 1:
        # If the length of the learned conflict clause is more than 1
        
        # Add the number of learned clauses in the stats object
        self.stats._num_learned_clauses += 1
        
        # Get the clause_id for this clause
        clause_id = self._num_clauses
        
        # Increment the number of clauses and add
        # the new clause to the clauses database
        self._num_clauses += 1
        self._clauses.append(conflict_clause)
        
        # Set the first 2 literals of the clause as its watchers.
        # Add the clause_id to the watch list of the first two literals of the clause
        self._clauses_watched_by_l.setdefault(conflict_clause[0],[]).append(clause_id)
        self._clauses_watched_by_l.setdefault(conflict_clause[1],[]).append(clause_id)
        
        # Set the list containing the 2 watchers as the literals watching the clause
        self._literals_watching_c[clause_id] = [conflict_clause[0],conflict_clause[1]]
        
        # If VSIDS decider is used
        if self._decider == "VSIDS":
            # For all the literals appearing in the conflict clause,
            # their score is increased by _incr
            for l in conflict_clause:
                self._lit_scores[l] += self._incr
                self._priority_queue.increase_update(l,self._incr)
                
            # Increase _incr by 0.75 to give more weightage
            # to the recent conflict clausing literal
            self._incr += 0.75
        
        # If MINISAT decider is used
        if self._decider == "MINISAT":
            # For all variables corresponding to the 
            # literals appearing in the clause, the
            # scores are increased by _incr
            for l in conflict_clause:
                var = self._get_var_from_literal(l)
                self._var_scores[var] += self._incr
                self._priority_queue.increase_update(var,self._incr)
            
            # To simulate the decay of all the previous var scores efficiently
            # (so as to give more weightage to the recent conflict clausing variables),
            # we divide the _incr by decay (instead of multiplying it to all the scores)
            self._incr /= self._decay
        
        # backtrack_level is the level to which the solver should jump back
        # conflict_level_literal is the single literal of the conflict level present in 
        # the conflict clause
        backtrack_level, conflict_level_literal = self._get_backtrack_level(conflict_clause,conflict_level)
        
        # Get the variable related to the conflict_level_literal
        conflict_level_var = self._get_var_from_literal(conflict_level_literal)
        
        # Check if conflict_level_literal is negative
        is_negative_conflict_lit = self._is_negative_literal(conflict_level_literal)
        
        # +++++++++++++++++++++++ NEED FOR THE ASSIGNMENT NODE ++++++++++++++++++++++++++++++++++
        # After backtracking, the added clause will imply that the conflict_level_literal should 
        # be true and so while backtracking, we add the clause as well as the assignment 
        # node that satisfies the conflict_level_literal. This latest assigned node will then
        # be used further to make more implications. This means when the new clause will be added, it 
        # will be satisfied because of this new assigned node and that's why we coan easily set the 
        # watchers as the first 2 literals as invariant is satisfied (because the clause is satisfied)
        
        # If conflict_level_literal is negative, its variable should be set False,
        # else it should be set True
        value_to_set = True
        if is_negative_conflict_lit:
            value_to_set = False
            
        # Create an assignment node with conflict_level_var, value_to_set
        # Set level as the backtrack level as ideally this is implied at that level
        # Set clause as the clause_id representing the conflict clause as this implication
        # is due to the conflict clause only
        node = AssignedNode(conflict_level_var,value_to_set,backtrack_level,clause_id)
        
        # Log if _is_log is true
        if self._is_log:
            print("Backtracking to level ",backtrack_level)
            print("Node after backtrack ",node)
        
        # return the backtrack level and the assignment node
        return backtrack_level,node
    else:
        # If the clause has only one literal, then it is the one
        # assigned at the conflict level (the first UIP). In this case,
        # we backtrack to level 0 and satisfy the conflict_level_literal
        # by adding an assignment node
        literal = conflict_clause[0]
        var = self._get_var_from_literal(literal)
        is_negative_literal = self._is_negative_literal(literal)
        
        # Get the assignment node corresponding to the literal
        assigned_node = self._variable_to_assignment_nodes[var]
        
        # Backtrack to level 0
        backtrack_level = 0

        # If conflict_level_literal is negative, its variable should be set False,
        # else it should be set True
        value_to_set = True
        if is_negative_literal:
            value_to_set = False
        
        # Create the node with var, value_to_set,backtrack_level(0)
        # Clause is set to None as this is implied by no clause 
        # (added to level 0)
        node = AssignedNode(var,value_to_set,backtrack_level,None)
        
        # return the backtrack level and the assignment node
        return backtrack_level,node
    
# Add the method to the SAT class    
SAT._analyze_conflict = analyze_conflict


# In[15]:


def backtrack(self,backtrack_level,node_to_add):
    '''
    Method used to backtrack the solver to the backtrack_level.
    It also adds the node_to_add to the assignment stack.
    
    Parameters:
        backtrack_level: the level to which the solver should backtrack(backjump)
        node_to_add: the implication node implied by the conflict clause to be added
        to the assignment stack at time of backtrack
        
    Return:
        None
    '''
    
    # sSet level of the solver to the backtrack_level
    self._level = backtrack_level
    
    # Remove all nodes at level greater than the backtrack_level fromt 
    # the assignment stack
    itr = len(self._assignment_stack)-1
    while True:
        if itr<0:
            # If the stack is empty, then break
            break
        if self._assignment_stack[itr].level <= backtrack_level: 
            # If a node with level less than equal to backtrack_level
            # is reached, then break
            break
        else:
            # delete the node from the variable to node dictionary
            del self._variable_to_assignment_nodes[self._assignment_stack[itr].var]
            
            # delete the node from the assignment stack
            node = self._assignment_stack.pop(itr)
            
            # If VSIDS decider is used, then when we unset the 
            # variables, we push the two literals correspoding
            # to the unset variable back into the priority queue
            # with their scores (priorities) as in the _lit_scores
            # array
            if self._decider == "VSIDS":
                self._priority_queue.add(node.var,self._lit_scores[node.var])
                self._priority_queue.add(node.var+self._num_vars,self._lit_scores[node.var+self._num_vars])
            
            # If MINISAT decider is used, then when we unset the 
            # variables, we push the unset variable back into the  
            # priority queue with their scores (priorities) as in 
            # the _lit_scores array
            if self._decider == "MINISAT":
                self._priority_queue.add(node.var,self._var_scores[node.var])
            
            # delete the node itself
            del node
            
            # move to the next node
            itr -= 1
    
    if node_to_add:
        # If node_to_add is not Nome
        # node_to_add is None in case when backtrack is used to restart the solver
        
        # Add the implied node to the variable to nodes dictionary
        self._variable_to_assignment_nodes[node_to_add.var] = node_to_add

        # Add the implied node to the assignment stack and
        # update the node's index to the position in the
        # stack at which it is pushed
        self._assignment_stack.append(node_to_add)
        node_to_add.index = len(self._assignment_stack)-1

        # If VSIDS decider is used, then when we assign the variable,
        # we remove the two literals corresponing to the variable
        # as in the priority queue, we always keep the unassigned
        # literals
        if self._decider == "VSIDS":
            self._priority_queue.remove(node_to_add.var)
            self._priority_queue.remove(node_to_add.var+self._num_vars)

        # If MINISAT decider is used
        if self._decider == "MINISAT":
            # Remove the assigned variable from the
            # priority queue as we keep only unassigned
            # variables in it
            self._priority_queue.remove(node_to_add.var)

            # Use the set value to update the
            # phase of the variable
            if node_to_add.value == False:
                self._phase[node_to_add.var] = 0
            else:
                self._phase[node_to_add.var] = 1

        # Increment the number of implications made 
        # in the stats object to count this implication
        # node
        self.stats._num_implications += 1

# Add the method to the SAT class
SAT._backtrack = backtrack


# The solve method implemented in the next cell is the main method which calls all the methods implemented
# above and solves the SAT problem.

# In[16]:


def solve(self,cnf_filename):
    '''
    The main method which is public in the SAT class
    and solves the SAT problem instance present in
    the passed filename. It prints "SAT" or "UNSAT"
    depending on whether the problem was satisfiable
    or not.
    
    Parameters:
        cnf_filename: Name of the file having the SAT formula (DIMACS CNF format) 
        to be solved
    
    Return:
        None
    '''
    
    # Set the input file name in the stats object
    self.stats._input_file = cnf_filename
    
    # Set the start time in the stats object
    self.stats._start_time = time.time()
    
    # Call the _read_dimacs_cnf_file method to 
    # read the input and process the clauses
    self._read_dimacs_cnf_file(cnf_filename)
    
    # Once read is complete, store the time
    self.stats._read_time = time.time()
    
    # Set the number of variables and clauses in the stats object
    self.stats._num_vars = self._num_vars
    self.stats._num_clauses = self._num_clauses
    

    if self.stats._result == "UNSAT":
        # The case where implications from the unary clauses
        # cause a conflict

        # Store the time when the result is 
        # ready to the stats object
        self.stats._complete_time = time.time()
    
    else:
        # We now solve the SAT problem
        
        # Indicating that BCP runs first time
        first_time = True

        # The main alogrithm loop
        while True:
            
            # Perform the Boolean Constraint Propogation untill there are no
            # conflicts
            while True:

                # Perform the BCP and store its return value in result
                temp = time.time()
                result = self._boolean_constraint_propogation(first_time)

                # Increase the time spend in BCP (stored in the stats object)
                self.stats._bcp_time += time.time()-temp

                # Break if no conflict
                if result == "NO_CONFLICT":
                    break

                # If "RESTART" is returned, it means
                # we need to restart the solver
                if result == "RESTART":
                    # Solver is restarted by undoing all the decisions
                    # and implications made starting from Level 1
                    # (As the level 0 decisions and implications are ones
                    # due to the unary clauses and so are fixed)
                    # So, we backtrack to level 0 to restart the solver
                    self._backtrack(0,None)
                    break

                # Set first_time to False as we want it 
                # to be true only once initially
                first_time = False

                # If there is a conflict, call _analyze_conflict method to 
                # analyze it
                temp = time.time()
                backtrack_level, node_to_add = self._analyze_conflict()

                # Increase the time spend in analyzing (stored in the stats object)
                self.stats._analyze_time += time.time()-temp

                # If backtrack level is -1, it means a conflict at level 0,
                # so the problem is UNSAT.
                if backtrack_level == -1:
                    # print the result
                    print("UNSAT")

                    # Store the result in the stats object
                    self.stats._result = "UNSAT"

                    # Store the time when the result is 
                    # ready to the stats object
                    self.stats._complete_time = time.time()

                    # Break out of the BCP loop
                    # as the problem is solved
                    break

                # Backtrack to the backtrack_level
                # node_to_add is added to the assignment stack in this
                # method and this woll be used to get further implications
                # when _boolean_constraint_propogation is called again in 
                # the next iteration
                temp = time.time()
                self._backtrack(backtrack_level,node_to_add)

                # Increase the time spend in backtracking (stored in the stats object)
                self.stats._backtrack_time += time.time()-temp
            
            if self.stats._result == "UNSAT":
                # Means that problem was proved to be UNSAT during BCP
                # so we break out of the external loop
                break
            
            # Set first_time to False as we want it 
            # to be true only once initially
            first_time = False

            # If all possible implications are made without conflicts,
            # then the solver decides on an unassigned variable
            # using the _decide method
            temp = time.time()
            var_decided = self._decide()

            # Increase the time spend in deciding (stored in the stats object)
            self.stats._decide_time += time.time()-temp

            if var_decided == -1:
                # If var_decided is -1, it means all the variables
                # have been assigned without any conflict and so the
                # input problem is satisfiable.
                # If this is not the case, then the external while loop
                # will again call the propogation loop and this cycle of
                # propogation and decision will continue until the 
                # problem is solved

                # print the result
                print("SAT")

                # Store the result in the stats object
                self.stats._result = "SAT"

                # Store the time when the result is 
                # ready to the stats object
                self.stats._complete_time = time.time()

                # Break out of the external while loop
                # as the problem is solved
                break

    # Create the Results directory if it does not exists
    if not os.path.isdir("Results"):
        os.mkdir("Results")
    
    # Extracts base file name from file path
    # eg. bmc-1.cnf from test/sat/bmc-1.cnf
    inputfile_basename = os.path.basename(cnf_filename)
    
    # Extracts test case name from the base file name
    # eg. bmc-1 from bmc-1.cnf
    input_case_name = os.path.splitext(inputfile_basename)[0]
    
    # Create the filename for stats file
    # eg. Results/stats_bmc-1.txt
    stats_file_name = "Results/stats_" + input_case_name + ".txt"
    
    # Set the stats file name to _output_statistics_file
    # stored in the statistics object
    self.stats._output_statistics_file = stats_file_name
    
    # Writing the stats to the stats file
    
    # Store the original standard output 
    original_stdout = sys.stdout
    
    # Set the standard output to point to the stats file
    sys.stdout = open(stats_file_name,"wt")
    
    # Call the print stats which actually writes in 
    # the file as standard output is directed towards the 
    # stats file
    self.stats.print_stats()
    
    # Restore the standard output once the stats file is
    # written
    sys.stdout = original_stdout
    
    if self.stats._result == "SAT":
        # If the problem is SAT
        
        # Create a filename for the assignment file
        # eg. Results/assgn_bmc-1.txt
        assgn_file_name = "Results/assgn_" + input_case_name + ".txt"
        
        # Set the assgn file name to _output_assignment_file
        # stored in the statistics object
        self.stats._output_assignment_file = assgn_file_name
        
        # Create a dictionary of variable to its assigned boolean
        # value
        assignment_dict = {}
        
        # Traverse the _variable_to_assignment_nodes and for each variable
        # store its set value in assignment_dict
        for var in self._variable_to_assignment_nodes:
            assignment_dict[var] = self._variable_to_assignment_nodes[var].value
        
        # Open the assignment file
        assgn_file = open(assgn_file_name,"w")
        
        # Write the dictionary into the file by
        # serializing it through json.dumps() method
        assgn_file.write(json.dumps(assignment_dict))
        
        # Close the assignment file
        assgn_file.close
        
    
# Add the method to the SAT class
SAT.solve = solve