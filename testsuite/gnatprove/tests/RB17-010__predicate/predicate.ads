package Predicate
with SPARK_Mode
is
   subtype P_Type is String
   with
      Predicate => P_Type'Length > 2;

   procedure P1 (P : in out P_Type);

   procedure P2 (P : out P_Type)
    with Pre => P'Length > 2;

end Predicate;
