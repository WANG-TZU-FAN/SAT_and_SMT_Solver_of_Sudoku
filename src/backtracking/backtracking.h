#ifndef BACKTRACKING_H
#define BACKTRACKING_H

#define NUM_LINE 9
#define NUM_SQUARE 3
#define DEBUG 0

int number_of_steps;

struct EntryData {
  int num;
  int row;
  int col;
};

struct EntryData sudokuMatrix [NUM_LINE][NUM_LINE];

/**Functions**/

/* 數獨題目 txt 檔的讀取 */
void fileInput(FILE *file_in, char* filePath,struct EntryData sudokuMatrix [NUM_LINE][NUM_LINE]){
   int i, j, convertedValue, counter = 0;
   char readValue;
   file_in = fopen(filePath, "r");
   for (i = 1; i <= NUM_LINE; i++){
      for (j = 1; j <= (NUM_LINE + NUM_LINE ); j++){
         // 讀取數值
         readValue = fgetc(file_in);
         // 存取該格的數值
         if((j % 2) != 0){
            convertedValue = atoi(&readValue);
            sudokuMatrix[i - 1][counter].num = convertedValue;
            counter++;
         }
      }
      counter = 0;
   }
   fclose(file_in);
}

/* 將數獨初始化為 9*9 的 0 矩陣 */
void reset(struct EntryData sudokuMatrix [NUM_LINE][NUM_LINE]){
   int i, j;
   number_of_steps = 0;
   for (i = 0; i < NUM_LINE; i++){
      for (j = 0; j < NUM_LINE; j++){
         sudokuMatrix[i][j].num = 0;
         sudokuMatrix[i][j].row = i;
         sudokuMatrix[i][j].col = j;
      }
   }
}

/* 輸出數獨的 9*9 矩陣 */
void print(struct EntryData sudokuMatrix [NUM_LINE][NUM_LINE]){
   int i, j;
   printf("\n");
   for (i = 0; i < NUM_LINE; i++){
      if((i % 3 == 0) && (i != 0)){
         printf("----------------------\n");
      }
      for (j = 0; j < NUM_LINE; j++){
         if((j % 3 == 0) && (j != 0)){
            printf(" |");
         }
         printf(" %d", sudokuMatrix[i][j].num);
      }
      printf("\n");   
   }
}

/* 確認輸入是否符合規則 */
int notValid(struct EntryData sudokuMatrix [NUM_LINE][NUM_LINE]){
   int violation = 0;
   int i, j, k, q;
   int begin_i, end_i, begin_j, end_j, counter_1 = 1;

   begin_i = 0;
   end_i =2;
   begin_j = 0;
   end_j = 2;
   // 比對九宮格中有沒有重複的數值
   while(end_i <= 8){
      if(counter_1 == 3){
         begin_i += 3;
         end_i += 3;
         begin_j = 0;
         end_j = 2;
         counter_1 = 1;
      }
      // 比對九宮格中有沒有重複的數值
      for(i  = begin_i; i <= end_i; i++){
         for(j = begin_j; j <= end_j; j++){
            // 0 是目前尚未填入數值的空格
            if(sudokuMatrix[i][j].num!=0){
               for(k=begin_i;k<=end_i; k++){
                  for(q=begin_j;q<=end_j; q++){
                     if(k!=i && q!=j){
                        if(sudokuMatrix[k][q].num == sudokuMatrix[i][j].num){
                        printf("\nERROR: Conflict between cells - sudoku[%d][%d]=%d and sudoku[%d][%d]=%d\n",i+1,j+1, sudokuMatrix[i][j].num, k+1,q+1, sudokuMatrix[k][q].num);
                        violation = 1;
                        return  violation;
                        }
                     }
                  }
               }
            }
         }
      }

      counter_1 ++;
      begin_j += 3;
      end_j += 3;
   }

   // 判斷 column 以及 row 中是否存在相同的數字
   // cell [i, j]
   for (i = 0; i < NUM_LINE; i++){
      for (j = 0; j < NUM_LINE; j++){
         // 0 是目前尚未填入數值的空格
         if(sudokuMatrix[i][j].num != 0){
         // 比對 row (row i) 中有沒有重複的數值
            for(k = 0; k < NUM_LINE; k++){
               if(k != j){
                  if(sudokuMatrix[i][k].num == sudokuMatrix[i][j].num){
                     printf("\nERROR: Conflict between cells - sudoku[%d][%d]=%d and sudoku[%d][%d]=%d\n",i+1,j+1, sudokuMatrix[i][j].num, i+1,k+1, sudokuMatrix[i][k].num);
                     violation = 1;
                     return  violation;
                  }
               }
            }
            // 比對 column (column j) 中有沒有重複的數值
            for(k = 0; k < NUM_LINE; k++){
               if(k != i){
                  if(sudokuMatrix[k][j].num == sudokuMatrix[i][j].num){
                     printf("\nERROR: Conflict between cells - sudoku[%d][%d]=%d and sudoku[%d][%d]=%d\n",i+1,j+1, sudokuMatrix[i][j].num, k+1,j+1, sudokuMatrix[k][j].num);
                     violation = 1;
                     return  violation;
                  }
               }
            }
         }
      }
   }

   
   return violation;
}

/* 找出原本沒有填入數值的空格（即輸入填 0 的部分） */
struct EntryData checkEmpty(struct EntryData sudokuMatrix [NUM_LINE][NUM_LINE]){
   int i, j;
   struct EntryData cell;

   cell.num = -1;

   for(i = 0; i < NUM_LINE; i++){
      for(j = 0; j < NUM_LINE; j++){
         if(sudokuMatrix[i][j].num == 0){
            // 只需要找到填 0 的那些座標
            return sudokuMatrix[i][j];
         }
      }
   }

   return cell;
}

/* 判斷該格能否填入數值 */
int checkPlacement(struct EntryData sudokuMatrix [NUM_LINE][NUM_LINE], int num, int row, int col){

   int i,j;
   int square_i,square_j;

   // 檢查 9 宮格
   square_i = row/3;
   square_j = col/3;
   for(i = 0;i < NUM_SQUARE; i++){
      for(j = 0;j < NUM_SQUARE; j++){
         if(sudokuMatrix[(square_i*3) + i][(square_j*3) + j].num == num){
            return 0;
         }
      }
   }
   // 檢查所有 row
   for(j = 0; j < NUM_LINE; j++){
      if(sudokuMatrix[row][j].num == num){
         return 0;
      }
   }

   // 檢查所有 column
   for(i = 0; i < NUM_LINE; i++){
      if(sudokuMatrix[i][col].num == num){
         return 0;
      }
   }
   
   return 1;
}

/* 如果我們找到解決方案則 return  1 否則 return 0 */
int solve(struct EntryData sudokuMatrix [NUM_LINE][NUM_LINE]){

   struct EntryData empty_cell;
   int k;

   empty_cell = checkEmpty( sudokuMatrix);
   // 不再有尚未填值的 entry
   if(empty_cell.num == -1){
         return 1;
   }
   else{
      for(k=1; k<=NUM_LINE; k++){
         if(checkPlacement(sudokuMatrix, k, empty_cell.row, empty_cell.col)){
            sudokuMatrix[empty_cell.row][empty_cell.col].num = k;
            number_of_steps++;

            if(solve(sudokuMatrix))
               return 1;
            // Backtracking
            sudokuMatrix[empty_cell.row][empty_cell.col].num = 0;
            number_of_steps++;
         }
      }
      // 如果 9 個數字都不能放在那個單元格上，那麼此題無解
      return 0;
   }

}

#endif // BACKTRACKING_H_INCLUDED
