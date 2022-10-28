#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/stat.h>
#include <sys/shm.h>
#include <sys/ipc.h>
#include <stdint.h>
#include <inttypes.h>
#include <math.h>

// Global Variables
int shmid;                // Shared memory id
int *shm;                 // Shared memory pointer
int N;                    // Size of grid
int S;                    // No of states
int two_states[2];        // When there are 2 states in NFA
int f = 0;                // Flag
char string[1024];        // Input String
long int length;          // Length of given String
__uint128_t tempA, tempB; // Temporary Variables

// A structure to implement a DFA with data members start states and final states.
typedef struct Definite_Finite_Automata
{
    __uint128_t start_states, final_states;
} Definite_Finite_Automata;

// Makes changes to the array and k
// Returns the new value of k
// prints the paths traversed
#define Explore(fptr) ({              \
    arr[k + 1] = a + N * b;           \
    print_the_path(fptr, arr, k + 1); \
    k++;                              \
    continue;                         \
})

// Checks whether the grid co-ordinates are inside the N*N grid
// Checks the validity of the coordinates
#define Check_Boundary(n, x, y) \
    (x >= 0 && x <= n - 1 && y >= 0 && y <= n - 1)

// Returns the next state of the NFA
// Checks whether fork needs to be performed a given node
bool create_Fork(int N, int x, int y, char s)
{

    if (s == '0' && Check_Boundary(N, x + 1, y) && Check_Boundary(N, x - 1, y))
        return true;
    else if (s == '1' && Check_Boundary(N, x, y + 1) && Check_Boundary(N, x, y - 1))
        return true;
    else
        return false;
}

// Prints the path traversed
//  fptr is the file pointer
//  arr is the array of grid co-ordinates
// Failed, accepted or exploring is printed based on the conditions
void print_the_path(FILE *fptr, int arr[], int curr)
{
    if (curr == length && arr[length] != N * N - 1)
        fprintf(fptr, "%s", "Failed at path: ");
    else if (curr == length && arr[length] == N * N - 1)
    {
        fprintf(fptr, "%s", "Accepted! Followed path: ");
        *shm = 1;
        // fprintf(fptr,"%s","\nDestroyed shm.bin\n");
    }
    else
    {
        fprintf(fptr, "[%d:%d] ", getppid(), getpid());
        fprintf(fptr, "%s", "Exploring Path: ");
    }
    for (int i = 0; i < curr + 1; i++)
    {
        fprintf(fptr, "%d ", arr[i]);
    }
    fprintf(fptr, "%s", "\n");
}

// Checks whether the string is accepted by the nfa or not (task 1)
void nfa_machine(FILE *fptr, char str[])
{
    length = strlen(str);
    int arr[length + 1];
    int a = 0, b = 0, k = 0;
    arr[0] = 0;
    print_the_path(fptr, arr, 0);
    while (k < length)
    {
        if ((shm = shmat(shmid, NULL, 0)) == (int *)-1)
        {
            exit(1);
        }
        if (*shm)
        {
            exit(0);
        }
        if (str[k] == '0')
        {
            if (!create_Fork(N, a, b, str[k]))
            {
                if (Check_Boundary(N, a - 1, b))
                {
                    a = a - 1;
                    Explore(fptr);
                }
                else if (Check_Boundary(N, a + 1, b))
                {
                    a = a + 1;
                    Explore(fptr);
                }
            }
            else
            {
                fflush(NULL);
                if (fork() == 0)
                {
                    // child
                    a = a + 1;
                    Explore(fptr);
                }
                else
                {
                    // parent
                    a = a - 1;
                    Explore(fptr);
                }
            }
        }
        if (str[k] == '1')
        {
            if (!create_Fork(N, a, b, str[k]))
            {
                if (Check_Boundary(N, a, b - 1))
                {
                    b = b - 1;
                    Explore(fptr);
                }
                else if (Check_Boundary(N, a, b + 1))
                {
                    b = b + 1;
                    Explore(fptr);
                }
            }
            else
            {
                fflush(NULL);
                if (fork() == 0)
                {
                    // child
                    b = b + 1;
                    Explore(fptr);
                }
                else
                {
                    // parent
                    b = b - 1;
                    Explore(fptr);
                }
            }
        }
    }
}

int find_states_nfa(int state, char s)
{
    int x, y, cnt = 0;
    x = state % N;
    y = (state - x) / N;
    if (s == '0')
    {
        if (Check_Boundary(N, x + 1, y))
        {
            two_states[cnt] = x + 1 + N * y;
            cnt++;
        }
        if (Check_Boundary(N, x - 1, y))
        {
            two_states[cnt] = x - 1 + N * y;
            cnt++;
        }
    }
    else if (s == '1')
    {
        if (Check_Boundary(N, x, y + 1))
        {

            two_states[cnt] = x + N * (y + 1);
            // printf("\n%d\n",two_states[cnt]);
            cnt++;
        }
        if (Check_Boundary(N, x, y - 1))
        {
            two_states[cnt] = x + N * (y - 1);
            cnt++;
        }
    }
    return cnt;
}

// Returns the DFA
int create_DFA(struct Definite_Finite_Automata *dfa_list, int k, __uint128_t st, __uint128_t store[], int p, char s)
{

    int cnt;
    dfa_list[k].start_states = st;
    dfa_list[k].final_states = 0;
    int remove_duplicates[S];
    int index = 0;
    for (int i = 0; i < S; i++)
    {
        tempA = st >> i;
        tempB = tempA & 1;
        if (tempB == 1)
        {
            cnt = find_states_nfa(i, s);
            if (cnt == 1)
            {
                int tflag = 0;
                for (int search = 0; search < index; search++)
                {
                    if (remove_duplicates[search] == two_states[0])
                        tflag = 1;
                }
                if (tflag == 0)
                {
                    dfa_list[k].final_states += pow((double)2, (double)two_states[0]);
                    remove_duplicates[index] = two_states[0];
                    index++;
                }
            }
            if (cnt == 2)
            {

                int tflag1 = 0, tflag2 = 0;
                for (int search = 0; search < index; search++)
                {
                    if (remove_duplicates[search] == two_states[0])
                        tflag1 = 1;
                    if (remove_duplicates[search] == two_states[1])
                        tflag2 = 1;
                }
                if (tflag1 == 0 && tflag2 == 0)
                {
                    dfa_list[k].final_states += (pow((double)2, (double)two_states[0]) + pow((double)2, (double)two_states[1]));
                    remove_duplicates[index] = two_states[0];
                    index++;
                    remove_duplicates[index] = two_states[1];
                    index++;
                }
                else if (tflag1 == 0 && tflag2 != 0)
                {
                    dfa_list[k].final_states += (pow((double)2, (double)two_states[0]));
                    remove_duplicates[index] = two_states[0];
                    index++;
                }
                else if (tflag1 != 0 && tflag2 == 0)
                {
                    dfa_list[k].final_states += (pow((double)2, (double)two_states[1]));
                    remove_duplicates[index] = two_states[1];
                    index++;
                }
            }
        }
    }
    f = 0;
    for (int search = 0; search < p; search++)
    {
        if (store[search] == dfa_list[k].final_states)
            f = 1;
    }
    if (f == 0)
    {
        store[p] = dfa_list[k].final_states;
        p++;
    }
    return p;
}

// using this algorithm we can convert the nfa to dfa
// the dfa created by this algorithm is the minimal dfa itself
void nfa_to_dfa_minimal(FILE *fptr)
{
    int k0 = 0, k1 = 0, snum = 1;
    Definite_Finite_Automata dfa_list_0[S];
    Definite_Finite_Automata dfa_list_1[S];
    __uint128_t store[S];
    dfa_list_0[k0].start_states = pow((double)2, (double)0);
    dfa_list_1[k1].start_states = pow((double)2, (double)0); // made change
    store[0] = pow((double)2, (double)0);
    for (int i = 0; i < S; i++)
    {
        snum = create_DFA(dfa_list_0, i, store[i], store, snum, '0');
        snum = create_DFA(dfa_list_1, i, store[i], store, snum, '1');
    }
    char finaldfa[2 * S + 1][S];
    for (int i = 0; i < 2 * S + 1; i++)
        for (int j = 0; j < S; j++)
        {
            finaldfa[i][j] = '0';
        }
    for (int i = 0; i < S; i++)
    {
        if (store[i] >= pow((double)2, (double)(S - 1)))
            finaldfa[0][i] = '1';
    }

    for (int i = 0; i < S; i++)
    {
        for (int j = 0; j < S; j++)
        {
            if (dfa_list_0[i].final_states == store[j])
                finaldfa[i + 1][j] = '1';
        }
    }
    for (int f_dfa = S; f_dfa < 2 * S; f_dfa++)
    {
        for (int f_dfa2 = 0; f_dfa2 < S; f_dfa2++)
        {
            if (dfa_list_1[f_dfa - S].final_states == store[f_dfa2])
                finaldfa[f_dfa + 1][f_dfa2] = '1';
        }
    }
    for (int i = 0; i < 2 * S + 1; i++)
    {
        for (int j = 0; j < S; j++)
        {
            fprintf(fptr, "%c ", finaldfa[i][j]);
        }
        fprintf(fptr, "%s", "\n");
    }
}

// Main function
int main(int argc, char *argv[])
{
    // Take input through the input.txt file
    FILE *fptr = fopen("input.txt", "r");
    fscanf(fptr, "%d", &N);
    N++;
    S = N * N;
    fscanf(fptr, "%s", string);
    fclose(fptr);
    if ((shmid = shmget(2041, 32, IPC_CREAT | 0666)) == -1)
    {
        perror("shmget");
        exit(1);
    }
    if ((shm = shmat(shmid, NULL, 0)) == (int *)-1)
    {
        exit(1);
    }
    *shm = 0;
    // create 3 file pointers
    FILE *fptr2, *fptr3, *fptr1;
    // open the output files of task 1
    fptr2 = fopen("2020A7PS1721H_T1.txt", "w");
    if (fptr2 == NULL)
    {
        printf("Error!!");
        exit(1);
    }
    else
    {
        nfa_machine(fptr2, string);
    }
    fclose(fptr2);

    fptr3 = fopen("2020A7PS1721H_T1.txt", "a");
    fputs("Destroyed Block: shm.bin", fptr3);
    fclose(fptr3);

    // file pointer prints the output of task 2
    fptr1 = fopen("2020A7PS1721H_T2.txt", "w");
    if (fptr1 == NULL)
    {
        printf("Error!!");
        exit(1);
    }
    else
    {
        nfa_to_dfa_minimal(fptr1);
    }
    fclose(fptr1);
    return 0;
}