import math

# List to store the luby numbers
l=[]

# Values that help to generate the Luby Sequence
mult = 1
minu = 0

def get_next_luby_number():
    """
    Method to get the next luby number

    Parameters:
        None
    
    Return:
        the next Luby number in the sequence
    """

    # Use the global variables
    global l
    global mult
    global minu

    size = len(l)

    # Index of the element to be generated,
    # pused into the list and returned
    to_fill = size+1

    if math.log(to_fill+1,2).is_integer():
        # If the index is of the form 2^K -1,
        # push mult into the queue and double it
        # for the next push
        l.append(mult)
        mult *= 2

        # This helps to fill the other indices
        minu = size+1
    else:
        # If the index is not of the form 2^K-1,
        # then the luby number is same as that at
        # the index to_fill-minu-1
        l.append(l[to_fill-minu-1])
    
    return l[size]

def reset_luby():
    """
    Method to reset the Luby Generator
    to initial conditions.

    Parameters:
        None
    
    Return:
        None
    """ 
    # Use the global variables
    global l
    global mult
    global minu

    # Reset it for the next use
    l=[]
    mult=1
    minu=0