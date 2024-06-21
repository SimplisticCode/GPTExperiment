#define cnt_is_zero (cnt == 0)
#define cnt_is_one (cnt == 1)
#define turn_is_true (turn == true)
#define turn_is_false (turn == false)
#define flag0_true (flag[0] == true)
#define flag0_false (flag[0] == false)
#define flag1_true (flag[1] == true)
#define flag1_false (flag[1] == false)
ltl mutual_exclusion { [](cnt <= 1) }
ltl progress_A { [](flag0_true -> <> cnt_is_one) }
ltl progress_B { [](flag1_true -> <> cnt_is_one) }
ltl turn_alternation_A { [](turn_is_false -> <> turn_is_true) }
ltl turn_alternation_B { [](turn_is_true -> <> turn_is_false) }
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
			:: turn == i;
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
