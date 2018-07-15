import java.nio.file.DirectoryStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Objects;
import java.util.Scanner;
import java.util.Set;
import java.util.StringTokenizer;
import java.util.function.Function;

public class Algorithm {

    private static final String EPSILON_CHAR = "?";
    private static final String START_VARIABLE = "Z";
    private static final String SPECIAL_CHAR = "\u10FD";
    private static final boolean LOG_ENABLE = false;

    private static class Rule {
        public String variable;
        public boolean isStarting;
        public List<String> rightSideTerms = new ArrayList<>();

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (!(o instanceof Rule)) return false;
            Rule rule = (Rule) o;
            return isStarting == rule.isStarting &&
                       Objects.equals(variable, rule.variable) &&
                       Objects.equals(rightSideTerms, rule.rightSideTerms);
        }

        @Override
        public int hashCode() {
            return Objects.hash(variable, isStarting, rightSideTerms);
        }
    }

    private List<String> inputData = new ArrayList<>();
    private List<String> terminals = new ArrayList<>();
    private List<String> variables = new ArrayList<>();
    private List<String> newVariables;
    private List<Rule> rules = new ArrayList<>();
    private List<Rule> newRules = new ArrayList<>();

    public void start() {
        readData();
        toCNF();
        toGNF();
    }

    private void toCNF() {
        addNewStartRule();
        removeNullProductions();
        removeUnitProductions();
        handelMoreThanTwoCharacters();
        handleTwoCharacters();
        printGrammar(rules);
    }

    private void toGNF() {
        changeVariables();
        printGrammar(newRules);
        alterBadRules();
        printGrammar(newRules);
        removeLeftRecursion();
        printGrammar(newRules);
        lastStep();
        printGrammar(newRules);
    }

    private void readData() {
        Scanner scanner = new Scanner(System.in);
        if (LOG_ENABLE) System.out.println("Please Enter Rules Count");
        int ruleCount = scanner.nextInt();
        for (int i = 0; i < ruleCount; i++) {
            if (LOG_ENABLE) System.out.println("Please Enter Rule #" + (i + 1));
            inputData.add(scanner.next());
        }

        boolean isFirst = true;
        for (String input : inputData) {
            StringTokenizer t1 = new StringTokenizer(input, "->");
            String var = t1.nextToken();
            StringTokenizer t2 = new StringTokenizer(t1.nextToken(), "|");
            List<String> terms = new ArrayList<>();
            while (t2.hasMoreTokens()) {
                terms.add(t2.nextToken());
            }

            boolean ruleFound = false;
            for (Rule rule : rules) {
                if (rule.variable.equals(var)) {
                    rule.rightSideTerms.addAll(terms);
                    ruleFound = true;
                    break;
                }
            }

            if (!ruleFound) {
                Rule rule = new Rule();
                rule.isStarting = isFirst;
                rule.rightSideTerms = terms;
                rule.variable = var;
                rules.add(rule);
            }
            isFirst = false;
        }

        initVariablesAndTerminals();
        removeUnnecessaryProductions();
        cleanRefreshRules();
    }

    private void addNewStartRule() {
        String startingRule = rules.get(0).variable;
        boolean occurredInRightSide = false;
        for (Rule rule : rules) {
            for (String term : rule.rightSideTerms) {
                if (term.contains(startingRule)) {
                    occurredInRightSide = true;
                    break;
                }
            }
        }

        if (!occurredInRightSide) return;

        Rule rule = new Rule();
        List<String> terms = new ArrayList<>();
        terms.add(rules.get(0).variable);
        rule.variable = START_VARIABLE;
        rule.rightSideTerms = terms;
        rule.isStarting = true;
        rules.get(0).isStarting = false;
        rules.add(0, rule);
    }

    private void removeUnitProductions() {
        boolean shouldContinue = true;
        while (shouldContinue) {
            shouldContinue = false;
            for (Rule rule : rules) {
                List<String> allVars = new ArrayList<>();
                for (String term : rule.rightSideTerms) {
                    if (variables.contains(term)) {
                        allVars.add(term);
                    }
                }

                List<String> shouldAddTerms = new ArrayList<>();
                for (String var : allVars) {
                    Rule currentRule = findRuleWithVar(var);
                    for (String term : currentRule.rightSideTerms) {
                        shouldAddTerms.add(term);
                        shouldContinue = true;
                    }
                }

                rule.rightSideTerms.addAll(shouldAddTerms);
                rule.rightSideTerms.removeAll(allVars);
            }

            cleanRefreshRules();
        }

        removeUnnecessaryProductions();
        cleanRefreshRules();
    }

    private void removeNullProductions() {
        boolean shouldContinue = true;
        while (shouldContinue) {
            shouldContinue = false;
            List<Rule> zeroProductionRules = new ArrayList<>();
            for (Rule rule : rules) {
                if (!rule.isStarting && rule.rightSideTerms.contains(EPSILON_CHAR)) {
                    zeroProductionRules.add(rule);
                }
            }
            for (Rule zeroProductRule : zeroProductionRules) {
                for (Rule rule : rules) {
                    List<String> newTerms = new ArrayList<>();
                    for (String term : rule.rightSideTerms) {
                        if (term.contains(zeroProductRule.variable)) {
                            shouldContinue = true;
                            List<Integer> indexes = findIndexesOf(term, zeroProductRule.variable);

                            int n = indexes.size();
                            for (int i = 0; i < (1 << n); i++) {
                                List<Integer> shouldChangeIndexes = new ArrayList<>();
                                for (int j = 0; j < n; j++) {
                                    if ((i & (1 << j)) > 0) {
                                        shouldChangeIndexes.add(indexes.get(j));
                                    }
                                }

                                StringBuilder builder = new StringBuilder(term);
                                for (int changeIndex : shouldChangeIndexes) {
                                    builder.setCharAt(changeIndex, EPSILON_CHAR.charAt(0));
                                }

                                String replacedEpsilonTerm = builder.toString().replace(EPSILON_CHAR, "");
                                if (replacedEpsilonTerm.length() == 0) {
                                    newTerms.add(EPSILON_CHAR);
                                } else {
                                    newTerms.add(replacedEpsilonTerm);
                                }
                            }
                        }
                    }

                    rule.rightSideTerms.addAll(newTerms);
                    removeDuplicates(rule.rightSideTerms);
                }

                zeroProductRule.rightSideTerms.remove(EPSILON_CHAR);
                cleanRefreshRules();
            }
        }
    }

    private void handelMoreThanTwoCharacters() {
        List<String> notUsed = readNotUsedChars();
        int count = 0;
        boolean shouldRepeat = true;
        while (shouldRepeat) {
            shouldRepeat = false;
            List<Rule> addingRules = new ArrayList<>();
            for (Rule rule : rules) {
                for (int i = 0; i < rule.rightSideTerms.size(); i++) {
                    String term = rule.rightSideTerms.get(i);
                    if (term.length() > 2) {
                        String t1 = term.charAt(0) + "";
                        String t2 = term.substring(1);

                        Rule foundRule = findRuleWithJustTerm(addingRules, t2);
                        if (foundRule == null) {
                            List<String> terms = new ArrayList<>();
                            terms.add(t2);
                            Rule newRule = new Rule();
                            newRule.isStarting = false;
                            newRule.variable = notUsed.get(count);
                            newRule.rightSideTerms = terms;
                            addingRules.add(newRule);

                            rule.rightSideTerms.set(i, t1 + notUsed.get(count));
                        } else {
                            rule.rightSideTerms.set(i, t1 + foundRule.variable);
                        }
                        shouldRepeat = true;
                        count++;
                    }
                }
            }

            rules.addAll(addingRules);
            initVariablesAndTerminals();
        }

    }

    private void handleTwoCharacters() {
        List<String> notUsed = readNotUsedChars();

        int count = 0;
        boolean shouldRepeat = true;
        while (shouldRepeat) {
            shouldRepeat = false;
            List<Rule> addingRules = new ArrayList<>();
            for (Rule rule : rules) {
                for (int i = 0; i < rule.rightSideTerms.size(); i++) {
                    String term = rule.rightSideTerms.get(i);

                    if (term.length() <= 1) {
                        continue;
                    }

                    String t1 = term.charAt(0) + "";
                    String t2 = term.charAt(1) + "";

                    boolean isT1Var = variables.contains(t1);
                    boolean isT2Var = variables.contains(t2);

                    if (term.length() == 2 && (!isT1Var || !isT2Var)) {

                        if (!isT1Var) {
                            Rule foundRule = findRuleWithJustTerm(addingRules, t1);
                            if (foundRule == null) {
                                List<String> terms = new ArrayList<>();
                                terms.add(t1);
                                Rule newRule = new Rule();
                                newRule.isStarting = false;
                                newRule.variable = notUsed.get(count);
                                newRule.rightSideTerms = terms;

                                addingRules.add(newRule);

                                rule.rightSideTerms.set(i, notUsed.get(count) + t2);
                            } else {
                                rule.rightSideTerms.set(i, foundRule.variable + t2);
                            }
                        }

                        if (!isT2Var) {
                            Rule foundRule = findRuleWithJustTerm(addingRules, t2);
                            if (foundRule == null) {
                                List<String> terms = new ArrayList<>();
                                terms.add(t2);
                                Rule newRule = new Rule();
                                newRule.isStarting = false;
                                newRule.variable = notUsed.get(count);
                                newRule.rightSideTerms = terms;

                                addingRules.add(newRule);

                                rule.rightSideTerms.set(i, t1 + notUsed.get(count));
                            } else {
                                rule.rightSideTerms.set(i, t1 + foundRule.variable);
                            }
                        }


                        shouldRepeat = true;
                        count++;
                    }
                }
            }

            rules.addAll(addingRules);
            initVariablesAndTerminals();
        }

    }

    private void changeVariables() {
        newVariables = new ArrayList<>(variables);
        int count = 0;

        for (Rule rule : rules) {
            List<String> terms = new ArrayList<>();
            terms.add(rule.variable);
            terms.addAll(rule.rightSideTerms);
            for (String term : terms) {
                for (int i = 0; i < term.length(); i++) {
                    String currentChar = String.valueOf(term.charAt(i));
                    int index = variables.indexOf(currentChar);
                    if (index != -1) {
                        if (!newVariables.get(index).contains("[")) {
                            newVariables.set(index, SPECIAL_CHAR + "[" + count + "]");
                            count++;
                        }
                    }
                }
            }
        }

        for (Rule rule : rules) {
            Rule newRule = new Rule();
            newRule.isStarting = rule.isStarting;
            newRule.variable = newVariables.get(variables.indexOf(rule.variable));
            List<String> newTerms = new ArrayList<>();
            for (String term : rule.rightSideTerms) {
                String newTerm = term;
                for (String var : variables) {
                    newTerm = newTerm.replace(var, newVariables.get(variables.indexOf(var)));
                }
                newTerms.add(newTerm);
            }
            newRule.rightSideTerms = newTerms;

            newRules.add(newRule);
        }
    }

    private void alterBadRules() {
        boolean shouldContinue = true;
        while (shouldContinue) {
            shouldContinue = false;
            for (Rule rule : newRules) {
                int i = findSubscriptOfVar(rule.variable);

                List<String> addingTerms = new ArrayList<>();
                List<String> removingTerms = new ArrayList<>();

                for (String term : rule.rightSideTerms) {

                    if (term.startsWith(SPECIAL_CHAR)) {

                        int j = findSubscriptOfVar(term);

                        String shouldAppend = term.substring(term.indexOf("]") + 1);

                        if (i > j) {

                            removingTerms.add(term);
                            Rule ruleJ = findNewRuleWithNum(j);
                            for (String termInJ : ruleJ.rightSideTerms) {
                                addingTerms.add(termInJ + shouldAppend);
                            }

                            shouldContinue = true;

                        }
                    }
                }

                rule.rightSideTerms.removeAll(removingTerms);
                rule.rightSideTerms.addAll(addingTerms);
                removeDuplicates(rule.rightSideTerms);
            }
        }
    }

    private int findSubscriptOfVar(String name) {
        int firstSubscriptStartIndex = name.indexOf("[") + 1;
        int firstSubscriptEndIndex = name.indexOf("]");
        String firstSubscript = name.substring(firstSubscriptStartIndex, firstSubscriptEndIndex);
        return Integer.parseInt(firstSubscript);
    }

    private void removeLeftRecursion() {
        List<String> notUsed = new ArrayList<>();
        int count = 0;
        for (int i = 'A'; i <= 'Z'; i++) {
            notUsed.add(String.valueOf((char) i));
        }

        List<Rule> addingRules = new ArrayList<>();

        for (Rule rule : newRules) {
            int i = findSubscriptOfVar(rule.variable);

            List<String> removingTerms = new ArrayList<>();
            List<String> addingTerms = new ArrayList<>();

            for (String term : rule.rightSideTerms) {

                if (term.startsWith(SPECIAL_CHAR)) {

                    int j = findSubscriptOfVar(term);

                    String continuee = term.substring(term.indexOf("]") + 1);

                    if (i == j) {
                        String varName = notUsed.get(count);
                        List<String> rightSideTerms = new ArrayList<>();
                        rightSideTerms.add(continuee + varName);
                        rightSideTerms.add(continuee);

                        Rule newRule = new Rule();
                        newRule.variable = varName;
                        newRule.isStarting = false;
                        newRule.rightSideTerms = rightSideTerms;
                        addingRules.add(newRule);

                        for (String termInRule : rule.rightSideTerms) {
                            if (termInRule.equals(term)) continue;

                            addingTerms.add(termInRule + varName);
                        }

                        removingTerms.add(term);
                        count++;
                    }
                }
            }

            rule.rightSideTerms.removeAll(removingTerms);
            rule.rightSideTerms.addAll(addingTerms);
        }

        newRules.addAll(addingRules);
    }

    private void lastStep() {

        int count = 0;
        for (Rule rule : newRules) {
            if (rule.variable.startsWith(SPECIAL_CHAR)) {
                count++;
            }
        }

        List<Rule> orderedRules = new ArrayList<>();
        for (int i = count - 1; i >= 0; i--) {
            orderedRules.add(findNewRuleWithNum(i));
        }

        for (Rule rule : newRules) {
            if (!rule.variable.startsWith(SPECIAL_CHAR)) {
                orderedRules.add(rule);
            }
        }


        // TODO : if this solution was not ok i can use while loop with a variable that show if loop should continue
        for (Rule rule : orderedRules) {
            List<String> removingTerms = new ArrayList<>();
            List<String> addingTerms = new ArrayList<>();

            for (String term : rule.rightSideTerms) {
                if (term.startsWith(SPECIAL_CHAR)) {
                    int j = findSubscriptOfVar(term);
                    String continuee = term.substring(term.indexOf("]") + 1);
                    Rule cRule = findNewRuleWithVar(SPECIAL_CHAR + "[" + j + "]");
                    for (String termInRule : cRule.rightSideTerms) {
                        addingTerms.add(termInRule + continuee);
                    }

                    removingTerms.add(term);

                }
            }

            rule.rightSideTerms.removeAll(removingTerms);
            rule.rightSideTerms.addAll(addingTerms);
        }
    }

    private Rule findNewRuleWithVar(String var) {
        for (Rule rule : newRules) {
            if (rule.variable.equals(var)) {
                return rule;
            }
        }
        return null;
    }

    private List<String> readNotUsedChars() {
        List<String> notUsed = new ArrayList<>();

        for (int i = 'A'; i <= 'Z'; i++) {
            String stChar = String.valueOf((char) i);
            boolean used = false;
            for (Rule rule : rules) {
                if (rule.variable.equals(stChar)) {
                    used = true;
                    break;
                }
            }

            if (!used) {
                notUsed.add(String.valueOf((char) i));
            }
        }

        return notUsed;
    }

    private void cleanRefreshRules() {
        for (Rule rule : rules) {
            removeDuplicates(rule.rightSideTerms);
        }
        rules.removeIf(rule -> rule.rightSideTerms.size() == 0);
        initVariablesAndTerminals();
    }

    private void removeUnnecessaryProductions() {
        rules.removeIf(rule -> !isAccessible(rules.get(0).variable, rule.variable));
    }

    private boolean isAccessible(String fromVar, String toVar) {

        Rule ruleWithVar = findRuleWithVar(fromVar);
        Set<String> allChars = new HashSet<>();
        allChars.add(fromVar);
        Set<String> newChars = new HashSet<>();
        while (true) {
            newChars = new HashSet<>();
            newChars.addAll(allChars);

            for (String ch : allChars) {
                Rule rule = findRuleWithVar(ch);
                for (String st : rule.rightSideTerms) {
                    for (String var : variables) {
                        if (st.contains(var)) {
                            newChars.add(var);
                        }
                    }
                }
            }

            if (allChars.equals(newChars)) {
                break;
            }

            allChars = newChars;
        }

        if (allChars.contains(toVar)) {
            return true;
        } else {
            return false;
        }
    }

    private boolean canGenerateTerminals(String fromVar) {
        return true;
    }

    private void printGrammar(List<Rule> rules) {
        for (Rule rule : rules) {
            System.out.print(rule.variable);
            System.out.print("->");
            for (int i = 0; i < rule.rightSideTerms.size(); i++) {
                if (i != 0) {
                    System.out.print("|");
                }
                System.out.print(rule.rightSideTerms.get(i));
            }
            System.out.println();
        }
        System.out.println();
    }

    private Rule findRuleWithJustTerm(List<Rule> smallRules, String term) {

        List<Rule> newRules = new ArrayList<>();
        newRules.addAll(rules);
        newRules.addAll(smallRules);

        for (Rule rule : newRules) {
            if (rule.rightSideTerms.size() > 1) continue;
            String t = rule.rightSideTerms.get(0);
            if (t.equals(term)) {
                return rule;
            }
        }
        return null;
    }

    private Rule findRuleWithVar(String var) {
        for (Rule rule : rules) {
            if (rule.variable.equals(var)) {
                return rule;
            }
        }
        return null;
    }

    private Rule findNewRuleWithNum(int num) {
        for (Rule rule : newRules) {
            if (rule.variable.contains(String.valueOf(num))) {
                return rule;
            }
        }
        return null;
    }

    private void removeDuplicates(List<String> list) {
        Set<String> set = new HashSet<>(list);
        list.clear();
        list.addAll(set);
    }

    private void initVariablesAndTerminals() {
        initVariablesAndTerminals(rules);
    }

    private void initVariablesAndTerminals(List<Rule> rules) {
        variables.clear();
        terminals.clear();

        for (Rule rule : rules) {
            variables.add(rule.variable);
        }

        for (Rule rule : rules) {
            for (String term : rule.rightSideTerms) {
                for (int i = 0; i < term.length(); i++) {
                    String stChar = String.valueOf(term.charAt(i));
                    if (!variables.contains(stChar) && !stChar.equals(EPSILON_CHAR) && !terminals.contains(stChar)) {
                        terminals.add(stChar);
                    }
                }
            }
        }
    }

    private List<Integer> findIndexesOf(String in, String of) {
        List<Integer> indexes = new ArrayList<>();
        int index = in.indexOf(of);
        if (index != -1)
            indexes.add(index);
        while (index >= 0) {
            index = in.indexOf(of, index + 1);
            if (index != -1) {
                indexes.add(index);
            }
        }
        return indexes;
    }
}