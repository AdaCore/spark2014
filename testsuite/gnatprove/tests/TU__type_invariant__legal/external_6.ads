with Type_Invariant_Legal_6; use Type_Invariant_Legal_6;

package External_6 with SPARK_Mode is

   function Read (X : T) return Integer;
   procedure Read (X : T);
   procedure Write (X : out T);
   procedure Read_Write (X : in out T);

end External_6;
