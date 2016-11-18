with Preconditions; use Preconditions;

package Decl_Only is

   procedure P_01;

   procedure P_02
     with Pre => Nonreturning_Precondition (4, 4);

   procedure P_03
     with Pre => Returning_Precondition (4, 4);



end Decl_Only;
