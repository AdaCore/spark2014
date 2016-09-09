with Type_Invariant_Legal_7; use Type_Invariant_Legal_7;

package External_7 with SPARK_Mode is

   function Read (X : T) return Integer;
   procedure Read (X : T);
   procedure Write (X : out T);
   procedure Read_Write (X : in out T);

end External_7;
