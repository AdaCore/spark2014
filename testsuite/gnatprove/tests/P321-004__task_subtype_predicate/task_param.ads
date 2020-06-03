package Task_Param is

   task type TT;

   procedure P (X : TT);

   function F (X : TT) return Boolean with Volatile_Function;

end Task_Param;
