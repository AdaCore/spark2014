package Dispatch_In_Contract with SPARK_Mode is
   type Root is tagged record
      F1 : Integer;
   end record;

   function Less_Than_Max (O : Root) return Boolean is
      (O.F1 < Integer'Last);

   procedure Incr (O : in out Root) with
     Pre'Class => Less_Than_Max (O);

   procedure Incr2 (O : in out Root) with
     Pre'Class => Less_Than_Max (O);

   type Child is new Root with record
      F2 : Integer;
   end record;

   function Less_Than_Max (O : Child) return Boolean is
      (O.F1 < Integer'Last and then O.F2 < Integer'Last);

   procedure Incr (O : in out Child) with
     Pre'Class => Less_Than_Max (O); -- Liskov fails here ? What about Incr2 ?
end Dispatch_In_Contract;
