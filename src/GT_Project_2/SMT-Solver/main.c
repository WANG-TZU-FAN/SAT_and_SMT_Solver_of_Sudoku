#include<stdio.h>
#include<stdlib.h>
#include<stdarg.h>
#include<memory.h>
#include<setjmp.h>
#include<string.h>
#include<z3.h>
#include<time.h>
#include "utilities.h"


#define LOG_Z3_CALLS

#ifdef LOG_Z3_CALLS
#define LOG_MSG(msg) Z3_append_log(msg)
#else
#define LOG_MSG(msg) ((void)0)
#endif


struct timespec diff(struct timespec start, struct timespec end) {
  struct timespec temp;
  if ((end.tv_nsec-start.tv_nsec)<0) {
    temp.tv_sec = end.tv_sec-start.tv_sec-1;
    temp.tv_nsec = 1000000000+end.tv_nsec-start.tv_nsec;
  } else {
    temp.tv_sec = end.tv_sec-start.tv_sec;
    temp.tv_nsec = end.tv_nsec-start.tv_nsec;
  }
  return temp;
}

/**
   \brief Create a variable using the given name and type.
*/
Z3_ast mk_var(Z3_context ctx, const char * name, Z3_sort ty)
{
    Z3_symbol   s  = Z3_mk_string_symbol(ctx, name);
    return Z3_mk_const(ctx, s, ty);
}

/**
   \brief Create a boolean variable using the given name.
*/
Z3_ast mk_int_var(Z3_context ctx, const char * name)
{
    Z3_sort ty = Z3_mk_int_sort(ctx);
    return mk_var(ctx, name, ty);
}


/**
   \brief Create a logical context.

   Enable model construction. Other configuration parameters can be passed in the cfg variable.

   Also enable tracing to stderr and register custom error handler.
*/
Z3_context mk_context_custom(Z3_config cfg, Z3_error_handler err)
{
    Z3_context ctx;

    Z3_set_param_value(cfg, "model", "true");
    ctx = Z3_mk_context(cfg);
    Z3_set_error_handler(ctx, err);

    return ctx;
}


/**
   \brief exit gracefully in case of error.
*/
void exitf(const char* message)
{
  fprintf(stderr,"BUG: %s.\n", message);
  exit(1);
}


/**
   \brief Simpler error handler.
 */
void error_handler(Z3_context c, Z3_error_code e)
{
    printf("Error code: %d\n", e);
    exitf("incorrect use of Z3");
}


/**
   \brief Display Z3 version in the standard output.
*/
void display_version()
{
    unsigned major, minor, build, revision;
    Z3_get_version(&major, &minor, &build, &revision);
    printf("Z3 %d.%d.%d.%d\n", major, minor, build, revision);
}

/**
   \brief Create a logical context.

   Enable model construction only.

   Also enable tracing to stderr and register standard error handler.
*/
Z3_context mk_context()
{
    Z3_config  cfg;
    Z3_context ctx;
    cfg = Z3_mk_config();
    ctx = mk_context_custom(cfg, error_handler);
    Z3_del_config(cfg);
    return ctx;
}



Z3_solver mk_solver(Z3_context ctx)
{
  Z3_solver s = Z3_mk_solver(ctx);
  Z3_solver_inc_ref(ctx, s);
  return s;
}

void del_solver(Z3_context ctx, Z3_solver s)
{
  Z3_solver_dec_ref(ctx, s);
}



/**
   \brief Check whether the logical context is satisfiable, and compare the result with the expected result.
   If the context is satisfiable, then display the model.
*/
void check(Z3_context ctx, Z3_solver s, Z3_lbool expected_result)
{
    Z3_model m      = 0;
    Z3_lbool result = Z3_solver_check(ctx, s);
    switch (result) {
    case Z3_L_FALSE:
        printf("\nThe puzzle is unsolvable\n");
        break;
    case Z3_L_UNDEF:
        printf("unknown\n");
        m = Z3_solver_get_model(ctx, s);
        if (m) Z3_model_inc_ref(ctx, m);
        printf("potential model:\n%s\n", Z3_model_to_string(ctx, m));
        break;
    case Z3_L_TRUE:
        /*m = Z3_solver_get_model(ctx, s);
        if (m) Z3_model_inc_ref(ctx, m);
        printf("sat\n%s\n", Z3_model_to_string(ctx, m));*/
        dumpModel(&ctx,s);
        publishZ3SudokuResult();
        
        break;
    }
    if (result != expected_result) {
        exitf("unexpected result");
    }
    if (m) Z3_model_dec_ref(ctx, m);
}
//
Z3_ast first_equal(Z3_context* ctx, Z3_ast variables [NUM_LINE][NUM_LINE]){

  int i,j,k,l, counter_total_constraint = 0;
  Z3_ast or_constraint, constraint,constraint1;
  int cell_possible_entries = 9;
  Z3_ast or_variables [cell_possible_entries];
  Z3_ast temp1, temp2;
  Z3_ast temp_or[2];
  
  Z3_ast total_constraint [10000]; //contains the constraint for each cell that are conjuncted
  Z3_ast total_constraint1;
  //printf("* CONSTRAINT ENFORCEMENT: At the beginning, the cell has a value .\n");
  
   //for each cell(i,j)
    for (i = 0; i < NUM_LINE; i++)
      for (j = 0; j < NUM_LINE; j++){ 
              if(variable_list[i][j].digit != 0){ // the cell is already assigned a content
                total_constraint[counter_total_constraint] = Z3_mk_eq(*ctx, variables[i][j], Z3_mk_unsigned_int64(*ctx, variable_list[i][j].digit, Z3_mk_int_sort(*ctx)));
                counter_total_constraint ++;  
              }
    }
     
   constraint = Z3_mk_and (*ctx, counter_total_constraint,total_constraint );

   //char* string2 = Z3_ast_to_string (*ctx, constraint);
             //printf("\n(assert = %s \n", string2);
    /*for (i = 0; i < NUM_LINE; i++)
      for (j = 0; j < NUM_LINE; j++){ 
              if(variable_list[i][j].digit != 0){ // the cell is already assigned a content
                constraint1 = Z3_mk_eq(*ctx, variables[i][j], Z3_mk_unsigned_int64(*ctx, variable_list[i][j].digit, Z3_mk_int_sort(*ctx)));
                char* string2 = Z3_ast_to_string (*ctx, constraint1);
                printf("(assert %s \n", string2); 
              }
    }*/

  return constraint;
 }



Z3_ast cell_value(Z3_context* ctx, Z3_ast variables [NUM_LINE][NUM_LINE]){

  int i,j,k,l, counter_total_constraint = 0;
  Z3_ast or_constraint, constraint,constraint1;
  int cell_possible_entries = 9;
  Z3_ast or_variables [cell_possible_entries];
  Z3_ast temp1, temp2;
  Z3_ast temp_and[2];
  
  Z3_ast total_constraint [10000]; //contains the constraint for each cell that are conjuncted
  Z3_ast total_constraint1 [2];
  //printf("* CONSTRAINT ENFORCEMENT: The value of each cell must be 1~9 .\n");
  
   //for each cell(i,j)
    for (i = 0; i < NUM_LINE; i++)
      for (j = 0; j < NUM_LINE; j++){ 
                temp1 = Z3_mk_gt(*ctx, variables[i][j], Z3_mk_unsigned_int64(*ctx, 0, Z3_mk_int_sort(*ctx))); 
                temp2 = Z3_mk_lt(*ctx, variables[i][j], Z3_mk_unsigned_int64(*ctx, 10, Z3_mk_int_sort(*ctx)));
                temp_and[0] = temp1;
                temp_and[1] = temp2;
                total_constraint[counter_total_constraint] = Z3_mk_and(*ctx, 2, temp_and);
                counter_total_constraint ++;
    }
     
   constraint = Z3_mk_and (*ctx, counter_total_constraint,total_constraint );
   printf("Constraints for the value of each cell must be 1~9:%d \n",counter_total_constraint);

   //char* string2 = Z3_ast_to_string (*ctx, constraint);
            //printf("TOTAL CONSTRAINT = %s \n", string2);

    //print
    /*for (i = 0; i < NUM_LINE; i++)
      for (j = 0; j < NUM_LINE; j++){ 
                total_constraint1[0] = Z3_mk_gt(*ctx, variables[i][j], Z3_mk_unsigned_int64(*ctx, 0, Z3_mk_int_sort(*ctx)));
                total_constraint1[1] = Z3_mk_lt(*ctx, variables[i][j], Z3_mk_unsigned_int64(*ctx, 10, Z3_mk_int_sort(*ctx)));
                counter_total_constraint ++;
                constraint1 = Z3_mk_and (*ctx, 2,total_constraint1 );
                char* string2 = Z3_ast_to_string (*ctx, constraint1);
                printf("(assert %s \n", string2);
    }*/


  return constraint;
 }


 Z3_ast once_each_row(Z3_context* ctx, Z3_ast variables [NUM_LINE][NUM_LINE]){

  int i,j,k,l, counter_total_constraint = 0;
  Z3_ast distinct_constraint, constraint,constraint1;
  int cell_possible_entries = 9;
  Z3_ast distinct_variables [cell_possible_entries];
  Z3_ast temp1, temp2;
  Z3_ast temp_and[2];
  
  Z3_ast total_constraint [10000]; //contains the constraint for each cell that are conjuncted
  Z3_ast total_constraint1 [2];
  //printf("* CONSTRAINT ENFORCEMENT: in each row, each digit must appear exactly once.\n");
  
   //for each cell(i,j)
    for (i = 0; i < NUM_LINE; i++){
      for (j = 0; j < NUM_LINE; j++){ 
                distinct_variables[j] = variables[i][j];
      }
      distinct_constraint = Z3_mk_distinct(*ctx, cell_possible_entries,distinct_variables);
      total_constraint[counter_total_constraint] = distinct_constraint;
      counter_total_constraint++;
    }
   constraint = Z3_mk_and (*ctx, counter_total_constraint,total_constraint );
   printf("Constraints for no the smae value in each row:%d \n",counter_total_constraint);

   //char* string2 = Z3_ast_to_string (*ctx, constraint);
            //printf("TOTAL CONSTRAINT =\n %s \n", string2);

    //print
    /*for (i = 0; i < NUM_LINE; i++)
      for (j = 0; j < NUM_LINE; j++){ 
                total_constraint1[0] = Z3_mk_gt(*ctx, variables[i][j], Z3_mk_unsigned_int64(*ctx, 0, Z3_mk_int_sort(*ctx)));
                total_constraint1[1] = Z3_mk_lt(*ctx, variables[i][j], Z3_mk_unsigned_int64(*ctx, 10, Z3_mk_int_sort(*ctx)));
                counter_total_constraint ++;
                constraint1 = Z3_mk_and (*ctx, 2,total_constraint1 );
                char* string2 = Z3_ast_to_string (*ctx, constraint1);
                printf("(assert %s \n", string2);
    }*/


  return constraint;
 }

 Z3_ast once_each_column(Z3_context* ctx, Z3_ast variables [NUM_LINE][NUM_LINE]){

  int i,j,k,l, counter_total_constraint = 0;
  Z3_ast distinct_constraint, constraint,constraint1;
  int cell_possible_entries = 9;
  Z3_ast distinct_variables [cell_possible_entries];
  Z3_ast temp1, temp2;
  Z3_ast temp_and[2];
  
  Z3_ast total_constraint [10000]; //contains the constraint for each cell that are conjuncted
  Z3_ast total_constraint1 [2];
  //printf("* CONSTRAINT ENFORCEMENT: in each column, each digit must appear exactly once.\n");
  
   //for each cell(i,j)
    for (j = 0; j < NUM_LINE; j++){
      for (i = 0; i < NUM_LINE; i++){ 
                distinct_variables[i] = variables[i][j];
      }
      distinct_constraint = Z3_mk_distinct(*ctx, cell_possible_entries,distinct_variables);
      total_constraint[counter_total_constraint] = distinct_constraint;
      counter_total_constraint++;
    }
   constraint = Z3_mk_and (*ctx, counter_total_constraint,total_constraint );
   printf("Constraints for no the smae value in each column:%d \n",counter_total_constraint);

   //char* string2 = Z3_ast_to_string (*ctx, constraint);
            //printf("TOTAL CONSTRAINT =\n %s \n", string2);

    //print
    /*for (i = 0; i < NUM_LINE; i++)
      for (j = 0; j < NUM_LINE; j++){ 
                total_constraint1[0] = Z3_mk_gt(*ctx, variables[i][j], Z3_mk_unsigned_int64(*ctx, 0, Z3_mk_int_sort(*ctx)));
                total_constraint1[1] = Z3_mk_lt(*ctx, variables[i][j], Z3_mk_unsigned_int64(*ctx, 10, Z3_mk_int_sort(*ctx)));
                counter_total_constraint ++;
                constraint1 = Z3_mk_and (*ctx, 2,total_constraint1 );
                char* string2 = Z3_ast_to_string (*ctx, constraint1);
                printf("(assert %s \n", string2);
    }*/


  return constraint;
 }

 Z3_ast once_each_square(Z3_context* ctx, Z3_ast variables [NUM_LINE][NUM_LINE]){

  int i,j,k,l,u,v, counter_total_constraint = 0;
  int begin_i, end_i, begin_j, end_j, counter_1 = 1, square = 1,count=0;
  Z3_ast distinct_constraint, constraint;
  int cell_possible_entries = 9*9;
  Z3_ast distinct_variables [cell_possible_entries];
  Z3_ast temp1, temp2;
  Z3_ast temp_or[2];
  
  Z3_ast total_constraint [10000]; //contains the constraint for each cell that are conjuncted
 
  //printf("* CONSTRAINT ENFORCEMENT: in each 3x3 square, each digit must appear once.\n");
      begin_i = 0;
      end_i =2;
      begin_j = 0;
      end_j = 2;
      while(end_i<=8){
       if(counter_1>3){
          begin_i+=3;
          end_i+=3;
          begin_j=0;
          end_j=2;
          counter_1 = 1;
       }
        if(square>9)
          break;


            for(i=begin_i;i<=end_i; i++){
               for(j=begin_j;j<=end_j; j++){
                   distinct_variables[count++] =  variables[i][j];//Xijk: possible assignment into a cell(i,j)

                }//end for i
             }//end for j
             distinct_constraint =  Z3_mk_distinct (*ctx, count--, distinct_variables); //The content can be k = 1,2, ..., or 9: Xij1 V ...V Xij9
             total_constraint[counter_total_constraint] = distinct_constraint; 
             counter_total_constraint++;
              count=0;

       counter_1 ++;
       begin_j+=3;
       end_j+=3;
       square++;


   }//end while
   constraint = Z3_mk_and (*ctx, counter_total_constraint,total_constraint );
   printf("Constraints for only a value in each cell:%d \n",counter_total_constraint);

   //char* string2 = Z3_ast_to_string (*ctx, constraint);
            //printf("TOTAL CONSTRAINT =\n %s \n", string2);

    //print
    /*for (i = 0; i < NUM_LINE; i++)
      for (j = 0; j < NUM_LINE; j++){ 
                total_constraint1[0] = Z3_mk_gt(*ctx, variables[i][j], Z3_mk_unsigned_int64(*ctx, 0, Z3_mk_int_sort(*ctx)));
                total_constraint1[1] = Z3_mk_lt(*ctx, variables[i][j], Z3_mk_unsigned_int64(*ctx, 10, Z3_mk_int_sort(*ctx)));
                counter_total_constraint ++;
                constraint1 = Z3_mk_and (*ctx, 2,total_constraint1 );
                char* string2 = Z3_ast_to_string (*ctx, constraint1);
                printf("(assert %s \n", string2);
    }*/


  return constraint;
 }



/**
  Main Function
*/
int main(int argc, char **argv) {
#ifdef LOG_Z3_CALLS
    Z3_open_log("z3.log");
#endif
    display_version();

    struct timespec time_start, time_end;
    double time_used_total;
    clock_gettime(CLOCK_MONOTONIC, &time_start);

    struct timespec time_generate_constraint_start, time_generate_constraint_end;
    double time_used_generate_constraint;

    struct timespec time_solve_start, time_solve_end;
    double time_used_solve;


    FILE *fp=NULL; //file pointer
    char* filePath = argv[1];
    int i,j,k, constraint_counter = 0;
    Z3_ast variables [NUM_LINE][NUM_LINE];
    Z3_ast constraints[10000];
    time_t time1,time2,time3;


    printf("   +------------------------+\n");
    printf("   | SUDOKU SOLVER WITH Z3! |\n");
    printf("   +------------------------+\n");

    resetSudokuMatrix(sudokuMatrix);//puts zeros in every cell of the sudoku array
    loadConfiguration(fp,filePath, sudokuMatrix);

    if(!checkViolation(sudokuMatrix))
        printf("\n\n  The initial SUDOKU set up is valid\n");
    else{
        printf("\n\n    The initial SUDOKU set up isn't valid\n");
        printSudokuMatrix(sudokuMatrix);
        return 0;
    }

    printf("\n    INITIAL SET UP! \n");
    printSudokuMatrix(sudokuMatrix);

    encodeSudoKuMatrix();

    //Here we can start building our Z3 Model
    Z3_context ctx = mk_context();
    Z3_solver  s = mk_solver(ctx);




    //modify
    //Z3_ast a = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "A"), Z3_mk_int_sort(ctx));

    //Constraint1: Only one digit per cell 
    printf("BUILDING CONSTRAINTS ... \n");
    clock_gettime(CLOCK_MONOTONIC, &time_generate_constraint_start);
    //
    //We dynamically create our 9*9*9=729 boolean variables
    for (i = 0; i < NUM_LINE; i++)
      for (j = 0; j < NUM_LINE; j++){
              variables[i][j] = mk_int_var(ctx, variable_list[i][j].var_name); 

    }
    constraints[constraint_counter] = first_equal(&ctx,variables);
    constraint_counter ++;

    constraints[constraint_counter] = cell_value(&ctx,variables);
    constraint_counter ++;

    constraints[constraint_counter] = once_each_row(&ctx,variables);
    constraint_counter ++;

    constraints[constraint_counter] = once_each_column(&ctx,variables);
    constraint_counter ++;

    constraints[constraint_counter] = once_each_square(&ctx,variables);
    constraint_counter ++;


  
    
  

   Z3_ast system = Z3_mk_and (ctx, constraint_counter,constraints );

   clock_gettime(CLOCK_MONOTONIC, &time_generate_constraint_end);
    struct timespec temp = diff(time_generate_constraint_start, time_generate_constraint_end);
    time_used_generate_constraint = temp.tv_sec + (double) temp.tv_nsec / 1000000.0;
   
   printf("ASSERTING Z3 SOLVER ... \n");  
    clock_gettime(CLOCK_MONOTONIC, &time_solve_start);
    Z3_solver_assert(ctx, s, system);
    check(ctx, s, Z3_L_TRUE);



    del_solver(ctx, s);
    Z3_del_context(ctx);

    clock_gettime(CLOCK_MONOTONIC, &time_solve_end);
    struct timespec temp1 = diff(time_solve_start, time_solve_end);
    time_used_solve = temp1.tv_sec + (double) temp1.tv_nsec / 1000000.0;

    printf("\n    FINAL SET UP! \n");
    printSudokuMatrix(sudokuMatrix);
    if(!checkViolation(sudokuMatrix))
        printf("\n  The final SUDOKU set up is valid\n");
    else{
        printf("\n    The final SUDOKU set up isn't valid\n");
        return 0;
    }

    clock_gettime(CLOCK_MONOTONIC, &time_end);
    struct timespec temp2 = diff(time_start, time_end);
    time_used_total = temp2.tv_sec + (double) temp2.tv_nsec / 1000000.0;
    printf("Generating constraints execution time of this program is: %f ms\n",time_used_generate_constraint);
    printf("SMT Solving execution time of this program is: %f ms\n",time_used_solve);
    printf("The program execution time of this program is: %f ms\n",time_used_total);
    return 0;

}