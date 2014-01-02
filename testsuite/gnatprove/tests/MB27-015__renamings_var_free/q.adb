package body Q
is

   function Get_V return T
   is
   begin
      return V;
   end Get_V;

   function Get_P (I : in T) return T
   is
   begin
      case I is
         when T'Last =>
            return T'First;
         when others =>
            return T'Succ (I);
      end case;
   end Get_P;


   function Get_Arr return Arr
   is
   begin
      return Arr_Obj;
   end Get_Arr;

   function Get_Arr_P1 (X : in Arr) return Arr
   is
   begin
      return X;
   end Get_Arr_P1;

   function Get_Arr_P2 (X : in Arr; I : in T) return Boolean
   is
   begin
      return X (I);
   end Get_Arr_P2;


   -- Direct ref to Arr_Obj, but indexing expression refs a variable
   S1 : Boolean renames Arr_Obj (Get_V);

   -- Ref to Arr_Obj via function call
   S2 : Boolean renames Get_Arr (1);

   -- Ref to Arr_Obj via function call AND variable index
   S3 : Boolean renames Get_Arr (Get_V);


   -- Function call with 1 param
   S4 : T renames Get_P (1); -- function call with static params

   S5 : T renames Get_P (V); -- function call with variable param

   S6 : T renames Get_P (Get_V); -- function call with variable param


   -- Function calls with 1 param, followed by a indexed component
   S7 : Boolean renames Get_Arr_P1 (Arr_Obj) (1); -- function call, var param

   S8 : Boolean renames Get_Arr_P1 (Get_Arr) (1); -- function call, var param

   S9 : Boolean renames Get_Arr_P1 (Arr_Obj) (V); -- function call, var params

   SA : Boolean renames Get_Arr_P1 (Get_Arr) (V); -- function call, var params

   SB : Boolean renames Get_Arr_P1 (Arr_Obj) (Get_V); -- function call, var params

   SC : Boolean renames Get_Arr_P1 (Get_Arr) (Get_V); -- function call, var params


   -- Cases where the outermost object is a constant array
   SD  : Boolean renames Null_Arr (1); -- all static - legal

   SE  : Boolean renames Null_Arr (V); -- variable index

   SF  : Boolean renames Null_Arr (Get_V); -- variable index

   S10 : Boolean renames Null_Arr (Get_P (1)); -- all static - legal

   S11 : Boolean renames Null_Arr (Get_P (V)); -- variable index

   S12 : Boolean renames Null_Arr (Get_P (Get_V)); -- variable index


   -- Cases with a function call with 2 args
   S13 : Boolean renames Get_Arr_P2 (Null_Arr, 1); -- static args

   S14 : Boolean renames Get_Arr_P2 (Null_Arr, Get_P (1)); -- static args

   S15 : Boolean renames Get_Arr_P2 (Arr_Obj, 1); -- 1 variable, 1 literal

   S16 : Boolean renames Get_Arr_P2 (Get_Arr, 1); -- 1 variable, 1 literal

   S17 : Boolean renames Get_Arr_P2 (Get_Arr, Get_P (1)); -- 1 variable, 1 static

   S18 : Boolean renames Get_Arr_P2 (Arr_Obj, V); -- 2 variables

   S19 : Boolean renames Get_Arr_P2 (Arr_Obj, Get_V); -- 2 variables

   S20 : Boolean renames Get_Arr_P2 (Get_Arr, V); -- 2 variables

   S21 : Boolean renames Get_Arr_P2 (Get_Arr, Get_V); -- 2 variables

end Q;
