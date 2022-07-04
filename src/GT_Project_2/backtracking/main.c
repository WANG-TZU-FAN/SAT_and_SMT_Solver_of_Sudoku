#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "backtracking.h"

// for calculating the execution time of this program
struct timespec diff(struct timespec start, struct timespec end) {
    struct timespec temp;
    if ((end.tv_nsec-start.tv_nsec)<0) {
        temp.tv_sec = end.tv_sec-start.tv_sec - 1;
        temp.tv_nsec = 1000000000+end.tv_nsec - start.tv_nsec;
    } else {
        temp.tv_sec = end.tv_sec-start.tv_sec;
        temp.tv_nsec = end.tv_nsec-start.tv_nsec;
    }
    return temp;
}

int main(int argc, char **argv)
{
    // to calculate the total execution time of one case
    struct timespec time_start, time_end;
    double time_used_total;
    clock_gettime(CLOCK_MONOTONIC, &time_start);

    struct timespec time_sub_1, time_sub_2;
    double time_used_solve;

    // file pointer
    FILE *fp = NULL;
    char* filePath = argv[1];
    int SOLVABLE;
    printf("\nProject_2: Sudoku Solver\n\n");
    
    reset(sudokuMatrix);
    fileInput(fp, filePath, sudokuMatrix);

    clock_gettime(CLOCK_MONOTONIC, &time_sub_1);
    if(notValid(sudokuMatrix)){
        printf("The initial Sudoku Matrix set up is not valid\n");
        printf("\n    Sudoku Puzzle \n");
        print(sudokuMatrix);
        return 0;
    }
    else{
        printf("The initial Sudoku Matrix set up is valid\n");
        printf("\n    Sudoku Puzzle \n");
        print(sudokuMatrix);
    }

    SOLVABLE = solve(sudokuMatrix);

    if(SOLVABLE){
        printf("\n\nSudoku puzzle can be solved in %d steps!\n", number_of_steps);
    }
    else{
        printf("\n\nSudoku puzzle can't be solved !\n");
    }
    clock_gettime(CLOCK_MONOTONIC, &time_sub_2);
    struct timespec temp = diff(time_sub_1, time_sub_2);
    time_used_solve = temp.tv_sec + (double) temp.tv_nsec / 1000000.0;
    printf("The solving time of this program is: %f ms\n", time_used_solve);

    printf("\n     FINAL RESULT\n");
    print(sudokuMatrix);

    if(notValid(sudokuMatrix)){
        printf("\n\n");
        printf("The puzzle is unsolvable\n");
    }
    else{
        printf("\n\n");
        printf("The puzzle is solvable\n");
    }
    
    clock_gettime(CLOCK_MONOTONIC, &time_end);
    struct timespec total = diff(time_start, time_end);
    time_used_total = total.tv_sec + (double) total.tv_nsec / 1000000.0;
    printf("The total program execution time of this program is: %f ms\n", time_used_total);
    
    return 0;
}
