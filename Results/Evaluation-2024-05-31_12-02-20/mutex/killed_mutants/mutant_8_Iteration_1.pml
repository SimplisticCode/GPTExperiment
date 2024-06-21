#define is_turn_true (turn == true)
#define is_turn_false (turn == false)
#define flag0_true (flag[0] == true)
#define flag0_false (flag[0] == false)
#define flag1_true (flag[1] == true)
#define flag1_false (flag[1] == false)
#define cnt_zero (cnt == 0)
#define cnt_one (cnt == 1)
#define cnt_not_more_than_one (cnt <= 1)
ltl mutual_exclusion { [] cnt_not_more_than_one }
ltl eventual_entry_A { [] (flag0_true -> <> cnt_one) }
ltl eventual_entry_B { [] (flag1_true -> <> cnt_one) }
ltl turn_alternation { [] (is_turn_true -> <> is_turn_false) && [] (is_turn_false -> <> is_turn_true) }
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
		turn = j;
		flag[i] = false;
	od;
}
