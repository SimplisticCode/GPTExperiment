#define in_critical_section (cnt == 1)
#define flagA_true (flag[0] == true)
#define flagB_true (flag[1] == true)
#define turnA (turn == false)
#define turnB (turn == true)
ltl mutual_exclusion { [] (cnt <= 1) }
ltl valid_cnt { [] (cnt == 0 || cnt == 1) }
ltl valid_flags { [] (flag[0] == true || flag[0] == false) && (flag[1] == true || flag[1] == false) }
ltl eventual_entry_A { [] (flagA_true -> <> in_critical_section) }
ltl eventual_entry_B { [] (flagB_true -> <> in_critical_section) }
ltl turn_alternation { [] (turnA -> <> turnB) && (turnB -> <> turnA) }
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
				((turn == j));
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
