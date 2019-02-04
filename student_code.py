import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################

        if isinstance(fact_or_rule, Fact): #if it is a fact
            if fact_or_rule not in self.facts: #check if the fact is in the KB
                return #return if there's no fact to retract
            else:
                real_fact = self._get_fact(fact_or_rule) # get the actual fact from kb
               
                if real_fact.supported_by:
                    if real_fact.asserted:
                        real_fact.asserted = False
                        return
                    else:
                        #can't retract from kB cuz its supported by other facts/rules
                        print("Can't be retracted")
                else: #fact is asserted
                    for item in real_fact.supports_facts: #for each fact that was supported by the retracted fact
                        item1 = self._get_fact(item).supported_by #get the pairs
                        for pair in item1:
                            if real_fact in pair:
                                item1.remove(pair)
                                pair.remove(real_fact)
                        if (len(item1) == 0): #there's no other facts to support 
                            if not item.asserted: #check if the item is asserted
                                self.kb_retract(item)

                    for item in real_fact.supports_rules: #for each rule that was supported by the retracted fact
                        item1 = self._get_rule(item).supported_by

                        for pair in item1:
                            if real_fact in pair:
                                item1.remove(pair)
                                pair.remove(real_fact)
                        if (len(item1) == 0):
                            if not item.asserted:
                                self.rules.remove(item)

                    self.facts.remove(real_fact)

                if (len(real_fact.supports_facts) == 0): #if it doesn't support any facts
                    if not real_fact.asserted and real_fact.supported_by: #if it is inferred and has support
                        return

                
        elif isinstance(fact_or_rule, Rule): # if it is a rule or anything else, don't change KB
            print("Cannot retract a rule")
            return
        else: #isnt a fact or rule, return
            print("not a fact or rule!")
            return


class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        rule_len = len(rule.lhs) #length of the lhs of the rule

        #check if the rule and fact have bindings
        matches = match(rule.lhs[0], fact.statement)
        if matches: 
            if (rule_len == 1): #if there is only 1 lhs statement, we add a new fact
                rf = []
                rf.append([fact, rule])
                new_fact = Fact(instantiate(rule.rhs, matches), rf) #make a new fact with the rule's lhs and the bindings
                print(new_fact)
                kb.kb_assert(new_fact) #add new fact to the KB
                fact.supports_facts.append(new_fact)
                rule.supports_facts.append(new_fact) #add the new fact to the support_facts list in both fact and rule
            else: #if there are multiple lhs statements, rule-carrying
                new_rule_list = [] #make a new list for the rule statements
                new_rule_list.append([instantiate(item, matches) for item in rule.lhs[1:]])
                new_rule_list.append(instantiate(rule.rhs, matches))
                new_rule = Rule(new_rule_list, [[rule, fact]])
                rule.supports_rules.append(new_rule)
                fact.supports_rules.append(new_rule)
                kb.kb_assert(new_rule)

