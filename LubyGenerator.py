import math

l=[]
mult = 1
minu = 0

def get_next_luby_number():
    global l
    global mult
    global minu

    size = len(l)
    to_fill = size+1

    if math.log(to_fill+1,2).is_integer():
        l.append(mult)
        minu = size+1
        mult *= 2
    else:
        l.append(l[to_fill-minu-1])
    
    return l[size]

def reset_luby():
    global l
    global mult
    global minu

    l=[]
    mult=1
    minu=0