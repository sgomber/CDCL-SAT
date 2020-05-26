
class PriorityQueue:
    def __init__(self,start_list):
        self.size = len(start_list)-1

        temp = start_list[1:]
        ctr = 1

        self.heap = []
        self.indices = []

        for x in temp:
            self.heap.append([x,ctr])
            self.indices.append(ctr-1)
            ctr += 1
        
        for i in range(int(self.size/2)-1,-1,-1):
            self.heapify(i)
    
    def swap(self,ind1,ind2):
        temp = self.heap[ind1]
        self.heap[ind1] = self.heap[ind2]
        self.heap[ind2] = temp

        p1 = self.heap[ind1][1]
        p1 -= 1
        p2 = self.heap[ind2][1]
        p2 -= 1

        temp = self.indices[p1]
        self.indices[p1]=self.indices[p2]
        self.indices[p2]=temp

    def heapify(self,node_index):
        maxp = self.heap[node_index][0]

        left_index = 2*node_index+1
        if left_index<self.size:
            pr = self.heap[left_index][0]
            if pr>maxp:
                maxp = pr
        
        right_index = 2*node_index+2
        if right_index<self.size:
            pr = self.heap[right_index][0]
            if pr>maxp:
                maxp = pr
        
        if maxp != self.heap[node_index][0]:
            if left_index<self.size and maxp == self.heap[left_index][0]:
                self.swap(left_index,node_index)
                self.heapify(left_index)
            else:
                self.swap(right_index,node_index)
                self.heapify(right_index)

    def get_top(self):
        if self.size == 0:
            return -1

        top_element = self.heap[0][1]
        self.swap(0,self.size-1)
        self.indices[self.heap[self.size-1][1]-1]=-1
        self.size -= 1
        self.heapify(0)

        return top_element

    def print_data(self):
        print("Size: ",self.size)
        print("Heap: ",self.heap[:self.size])
        print("Indices: ",self.indices)

    
    def increase_update(self,key,value):
        if self.indices[key-1] == -1:
            return
        
        pos = self.indices[key-1]
        self.heap[pos][0] += value

        par=pos
        while par!=0:
            temp = par
            par = int((par-1)/2)
            if self.heap[temp][0] > self.heap[par][0]:
                self.swap(temp,par)
            else:
                break
    
    def remove(self,key):
        if self.indices[key-1] == -1:
            return

        pos = self.indices[key-1]
        this_node_pr = self.heap[pos][0]
        final_node_pr = self.heap[self.size-1][0]
        self.swap(pos,self.size-1)
        self.size -= 1

        if final_node_pr > this_node_pr:
            par = pos
            while par!=0:
                temp = par
                par = int((par-1)/2)
                if self.heap[temp][0] > self.heap[par][0]:
                    self.swap(temp,par)
                else:
                    break
        elif this_node_pr > final_node_pr:
            self.heapify(pos)
            
    def add(self,key,value):
        self.heap[self.size] = [0,key]
        self.indices[key-1] = self.size
        self.size += 1
        self.increase_update(key,value)