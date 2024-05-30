#define flag0_true (flag[0] == true)
#define flag1_true (flag[1] == true)
#define flag0_false (flag[0] == false)
#define flag1_false (flag[1] == false)
#define turn_A (turn == false)
#define turn_B (turn == true)
#define cnt_0 (cnt == 0)
#define cnt_1 (cnt == 1)
ltl mutual_exclusion { [](cnt <= 1) }
ltl eventual_entry_A { [](flag0_true -> <> cnt_1) }
ltl eventual_entry_B { [](flag1_true -> <> cnt_1) }
ltl turn_alternation { []((turn_A -> <> turn_B) && (turn_B -> <> turn_A)) }
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
