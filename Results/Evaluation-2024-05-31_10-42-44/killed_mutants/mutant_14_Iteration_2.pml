#define in_critical_section (cnt == 1)
#define flagA_true (flag[0] == true)
#define flagB_true (flag[1] == true)
#define turnA (turn == false)
#define turnB (turn == true)
#define flagA_false (flag[0] == false)
#define flagB_false (flag[1] == false)
ltl mutual_exclusion { [] (cnt <= 1) }
ltl valid_cnt { [] (cnt == 0 || cnt == 1) }
ltl valid_flags { [] (flag[0] == true || flag[0] == false) && (flag[1] == true || flag[1] == false) }
ltl eventual_entry_A { [] (flagA_true -> <> in_critical_section) }
ltl eventual_entry_B { [] (flagB_true -> <> in_critical_section) }
ltl turn_alternation { [] (turnA -> <> turnB) && (turnB -> <> turnA) }
ltl flag_reset_A { [] (in_critical_section -> <> flagA_false) }
ltl flag_reset_B { [] (in_critical_section -> <> flagB_false) }
ltl processB_execution { [] (flagB_true -> <> in_critical_section) }
ltl turn_assignment_A { [] (in_critical_section -> <> turnB) }
ltl turn_assignment_B { [] (in_critical_section -> <> turnA) }
bool turn;
bool flag[2];
byte cnt;
active proctype ProcessA(){
	int i = 0;
	int j = 1;
	do
	:: true;
		flag[i] = true;
		do
		:: flag[j];
			if
			:: turn == j;
				flag[i] = false;
				!(turn == j);
				flag[i] = true;
			:: else;
			fi;
		:: else;
			break;
		od;
		cnt++;
		assert(cnt == 1);
		cnt--;
		turn = j;
		flag[i] = false;
	od;
}
active proctype ProcessB(){
	int i = 1;
	int j = 0;
	do
	:: true;
		flag[i] = true;
		do
		:: flag[j];
			if
			:: turn == j;
				flag[i] = false;
				!(turn == j);
				flag[i] = true;
			:: else;
			fi;
		:: else;
			break;
		od;
		cnt++;
		assert(cnt == 1);
		cnt--;
		turn = i;
		flag[i] = false;
	od;
}
