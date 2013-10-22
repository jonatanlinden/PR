#!/usr/bin/env python

import gdb

class SkiplistPrintCommand(gdb.Command):
    """Iterate and print a list.

skip <EXPR> [MAX]

Given a list EXPR, iterate though the list nodes' ->next pointers, printing
each node iterated. We will iterate thorugh MAX list nodes, to prevent
infinite loops with corrupt lists. If MAX is zero, we will iterate the
entire list.

List nodes types are expected to have a member named "next". List types
may be the same as node types, or a separate type with an explicit
head node, called "head"."""

    MAX_ITER = 10

    def __init__(self):
        super(SkiplistPrintCommand, self).__init__("skiplist-print", gdb.COMMAND_DATA, gdb.COMPLETE_SYMBOL)

    def invoke(self, _args, from_tty): #stop_iter): #stop_key):
        args = gdb.string_to_argv(_args)
        start_node = args[0]

        if len(args) == 2:
            max_iter = int(args[1])
        else:
            max_iter = self.MAX_ITER

        
        p_node_t = gdb.lookup_type('node_t').pointer()
        long_t = gdb.lookup_type('long')


        head = gdb.parse_and_eval(start_node)

        fnames = [ f.name for f in head.type.fields() ]

        print fnames

        # handle lists with a separate list type....

        print "list@%s: %s" % (head.address, head)
        print head.dereference()
        node = head['next'].dereference()
        node = gdb.Value(node).cast(long_t)
        node = node & ~1
        node = gdb.Value(node).cast(p_node_t).dereference()
        print node
        i = 1
#        while node['k'] < stop_key:
        while i < max_iter:
#            print "node@%s: %s #%d" % (node, node.dereference(), i)

            node = node['next'].dereference()
            node = gdb.Value(node).cast(long_t)
            node = node & ~1
            node = gdb.Value(node).cast(p_node_t).dereference()
            print node
            i += 1

SkiplistPrintCommand()
