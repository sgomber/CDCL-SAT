
class PriorityQueue:
    """
    Class to implement the Priority Queue.
    """

    def __init__(self,start_list):
        """
        Constructor of the priority queue class.

        Parameters:
            start_list: the initially array of scores which are to be pushed in
                        the priority queue
        
        Return:
            the initialized priority queue object
        """

        # The first element is removed as it is not related
        # to any variable or literal
        self.size = len(start_list)-1
        temp = start_list[1:]

        # Array that stores the heap
        # Each element in the heap is of the form
        # [priority,element] where priority is the
        # priority of the element and the heap is
        # max heap with respect to the priority scores
        self.heap = []

        # Array that maps elements to their indices
        # in the heap
        self.indices = []

        ctr = 1
        for x in temp:
            # For all elements in the array,
            # push the [priority,ctr] pair in
            # the heap
            self.heap.append([x,ctr])
            self.indices.append(ctr-1)
            ctr += 1
        
        # This is the basic method to convert an array into
        # heap (by calling heapify in reverse order from first
        # half elements)
        for i in range(int(self.size/2)-1,-1,-1):
            self.heapify(i)
    
    def swap(self,ind1,ind2):
        """
        Swaps elements poined by ind1 and ind2 in the heap.

        Parameters:
            ind1: index in the heap of first element to be swapped
            ind2: index in the heap of the second element to be swapped
        
        Return:
            None
        """

        # Swap the nodes in the heap array
        temp = self.heap[ind1]
        self.heap[ind1] = self.heap[ind2]
        self.heap[ind2] = temp

        # Swap the indices of the nodes
        # in the indices array as the nodes
        # swapped and so their indices also must
        # be swapped
        p1 = self.heap[ind1][1]
        p1 -= 1
        p2 = self.heap[ind2][1]
        p2 -= 1
        temp = self.indices[p1]
        self.indices[p1]=self.indices[p2]
        self.indices[p2]=temp

    def heapify(self,node_index):
        """
        The well known heapify method. Takes in a
        node_index and assuming that its children subtress
        are perfect max heaps, this method converts the whole
        tree rooted at node_index into a max heap.

        Parameters:
            node_index: root of the tree which has to be heapified
        
        Return:
            None
        """

        # Calculate the max priority between the node,
        # its left and its right child

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
            # If max priority is not of root

            if left_index<self.size and maxp == self.heap[left_index][0]:
                # If max priority is of the left node,
                # swap left node with root node 
                # and recursively call heapify on the left node
                # to make it a nax heap
                self.swap(left_index,node_index)
                self.heapify(left_index)
            else:
                # If max priority is of the right node,
                # swap right node with root node 
                # and recursively call heapify on the right node
                # to make it a nax heap
                self.swap(right_index,node_index)
                self.heapify(right_index)

    def get_top(self):
        """
        Get the top element (with max priority) from the queue.

        Parameters:
            None
        
        Return:
            -1 if queue is empty else the element with the highest priority
        """

        # If queue is empty, return -1
        if self.size == 0:
            return -1

        # Top element is the element in heap[0]
        top_element = self.heap[0][1]

        # To remove the first element, we swap it with the last
        # element, reduce size of queue by 1 and call
        # heapify(0) to maintain the heap structure
        self.swap(0,self.size-1)
        self.indices[self.heap[self.size-1][1]-1]=-1
        self.size -= 1
        self.heapify(0)

        return top_element

    def print_data(self):
        """
        Method to print the data structures of the class.

        Parameters:
            None
        
        Return:
            None
        """
        print("Size: ",self.size)
        print("Heap: ",self.heap[:self.size])
        print("Indices: ",self.indices)

    
    def increase_update(self,key,value):
        """
        Method takes in a key and value and for the element that matches the key,
        its priority is increased by value.
        
        Parameters:
            key: element whose priority is to be increased
            value: amount by which the priority has to be increased
        
        Return:
            None
        """
        if self.indices[key-1] == -1:
            return
        
        pos = self.indices[key-1]
        
        # Increase its priority by value
        self.heap[pos][0] += value

        # To maintain the heap structure, traverse the heap 
        # from this node upwards and replace it with its parent 
        # till its parent is bigger than it. 
        # (This is needed as increasing the priority
        # can disrupt the heap structure)
        par=pos
        while par!=0:
            temp = par
            par = int((par-1)/2)
            if self.heap[temp][0] > self.heap[par][0]:
                self.swap(temp,par)
            else:
                break
    
    def remove(self,key):
        """
        Remove the element pointed by key from the queue.

        Parameters:
            key: the element to be removed from the queue
        
        Return:
            None
        """
        if self.indices[key-1] == -1:
            return

        # Replace the node to be deleted with 
        # the final node
        pos = self.indices[key-1]
        this_node_pr = self.heap[pos][0]
        final_node_pr = self.heap[self.size-1][0]
        self.swap(pos,self.size-1)
        self.size -= 1
        self.indices[key-1] = -1


        if final_node_pr > this_node_pr:
            # If the replaced node has a higher priority,
            # then the deleted node, traverse the heap upwards
            # and replace the node with its parent unti 
            # its parent is bigger than it. This is done to 
            # maintain the heap structure.
            par = pos
            while par!=0:
                temp = par
                par = int((par-1)/2)
                if self.heap[temp][0] > self.heap[par][0]:
                    self.swap(temp,par)
                else:
                    break
        elif this_node_pr > final_node_pr:
            # If replaced node has a lower priority than the 
            # removed node,then use heapify to maintain the
            # heap structure
            self.heapify(pos)

    def add(self,key,value):
        """
        Method to add an element (key) with priority value
        into the priority queue.

        Parameters:
            key: the element to be added in the priority queue
            value: the priority value of the element to be added
        
        Return:
            None
        """

        # Push the key to the last position with priority 0
        self.heap[self.size] = [0,key]
        self.indices[key-1] = self.size

        # Increase the heap size
        self.size += 1

        # Call the increase update method to increase
        # the priority of key from 0 to value
        self.increase_update(key,value)