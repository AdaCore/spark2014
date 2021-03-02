package Might_Not_Return_Callee with SPARK_Mode is
   procedure P with Annotate => (GNATprove, Might_Not_Return);
end Might_Not_Return_Callee;
