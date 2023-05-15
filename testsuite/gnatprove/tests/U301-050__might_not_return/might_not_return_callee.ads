package Might_Not_Return_Callee with SPARK_Mode is
   procedure P with Always_Terminates => False;
end Might_Not_Return_Callee;
