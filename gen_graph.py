import random
import networkx as nx
import math
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt


def getAncestors(node, graph):
    queue = [node]
    ancestors = set()
    while queue:
        curr_node = queue.pop()
        for n in graph:
            if graph[n].intersection(set(queue)):
                queue.append(n)
                ancestors.add(n)
    return ancestors

def createGraph(m, p, q, num_iterations):
    d = {}
    for i in range(num_iterations):
        d['v'+str(i)] = set()
        if m > len(d.keys()):
            maybe_connect = d.keys()
        else:
            maybe_connect = random.sample(d.keys(), m)
        for x in maybe_connect:
            if random.random() < p:
                d['v'+str(i)].add(x)
            for ancestor in getAncestors(x, d):
                if random.random() < q:
                    d['v'+str(i)].add(ancestor)
    return d

def plotGraph(graph, label=False, figsize=(4,4)):
    assert(graph.order() != 0)
    plt.plot()
    plt.figure(figsize=figsize)
    nx.spring_layout(graph, k=5/math.sqrt(graph.order()))
    nx.draw(graph, with_labels=label, node_size = 50)
    l,r = plt.xlim()
    plt.xlim(l-.2,r+.2)
