#define in_critical_section (cnt == 1)
#define processA_wants (flag[0] == true)
#define processB_wants (flag[1] == true)
#define turnA (turn == false)
#define turnB (turn == true)
ltl valid_cnt { [](cnt == 0 || cnt == 1) }
ltl mutual_exclusion { [](cnt <= 1) }
ltl processA_eventually_critical { [](processA_wants -> <> in_critical_section) }
ltl processB_eventually_critical { [](processB_wants -> <> in_critical_section) }
ltl processA_turn { [](processA_wants -> <> turnA) }
ltl processB_turn { [](processB_wants -> <> turnB) }
bool turn;
bool flag[2];
byte cnt;

active proctype ProcessA()
{
    int i = 0; // Assuming process A has a fixed id of 0
    int j = 1;
    do
    :: true -> // Replaces the againA label for repetition
        flag[i] = true;
        do
        :: flag[j] ->
            if
            :: turn == j ->
                flag[i] = false;
                !(turn == j);
                flag[i] = true
            :: else
            fi
        :: else ->
            break
        od;

        cnt++;
        assert(cnt == 1); /* critical section */
        cnt--;

        turn = j;
        flag[i] = false;
    od; // End of outer loop for continuous execution
}

active proctype ProcessB()
{
    int i = 1; // Assuming process B has a fixed id of 1
    int j = 0;
    do
    :: true -> // Replaces the againB label for repetition
        flag[i] = true;
        do
        :: flag[j] ->
            if
            :: turn == j ->
                flag[i] = false;
                !(turn == j);
                flag[i] = true
            :: else
            fi
        :: else ->
            break
        od;

        cnt++;
        assert(cnt == 1); /* critical section */
        cnt--;

        turn = j;
        flag[i] = false;
    od; // End of outer loop for continuous execution
}