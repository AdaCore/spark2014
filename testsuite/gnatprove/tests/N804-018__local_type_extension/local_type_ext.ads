package Local_Type_Ext with
  SPARK_Mode
is
   type T is tagged null record;

   function F return T'Class;

   procedure P (X : T'Class; Blah : Boolean);

end Local_Type_Ext;
