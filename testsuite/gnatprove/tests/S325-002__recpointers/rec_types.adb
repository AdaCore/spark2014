package body Rec_Types with SPARK_Mode is
   package body Test1 is
      procedure P_Tree is
         A : Tree_Array_Access :=
           new Tree_Array (1 .. 10);
         X : Tree := new Tree_Node'(Val => 0, Next => A);
      begin
         for I in 1 .. 10 loop
            X.Next (I) := new Tree_Node'(Val => I, Next => null);
         end loop;
      end P_Tree;
   end Test1;

   package body Test2 is
      procedure P_Tree is
         A : Tree_Array (1 .. 10);
         X : Tree := new Tree_Node'(D => 10, Val => 0, Next => A);
      begin
         for I in 1 .. 10 loop
            pragma Loop_Invariant (X /= null and then X.D = 10);
            declare
               Next : Tree_Array (1 .. I);
            begin
               X.Next (I) := new Tree_Node'(D => I, Val => I, Next => Next);
            end;
         end loop;
      end P_Tree;
   end Test2;

   package body Test3 is
      procedure P_Tree is
         X : Tree_2 := new Tree_2_Node'(Val => 0, others => null);
      begin
         X.Left := new Tree_3_Node'(Val => 1, others => null);
         X.Left.Left := new Tree_2_Node'(Val => 2, others => null);
      end P_Tree;
   end Test3;
end;
