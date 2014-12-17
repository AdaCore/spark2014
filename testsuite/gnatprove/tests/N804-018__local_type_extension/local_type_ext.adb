package body Local_Type_Ext with
  SPARK_Mode
is
   function F return T'Class is
      type Local is new T with null record ;

      X : Local;
      function G return T'Class is
      begin
         return X; -- no problem with this return statement
      end;
   begin
      return G; -- but this one fails an accessibility check
   end;

   procedure P (X : T'Class; Blah : Boolean) is
      type Local is new T with null record;

      Xx : Local;

      function Is_Local (Y : T'Class) return Boolean is
      begin
         return Y in Local;
      end;

   begin
      if Blah then
         P (Xx, Blah);
      end if;
      if Is_Local (X) then
         return;
      end if;
   end P;

   procedure NOK is
      type T is tagged null record;
      type E is interface;
   begin
      declare
         type Local is new T with null record;
         type T2 is tagged null record;
         type Local2 is new T2 and E with null record;
      begin
         null;
      end;
   end NOK;

   procedure OK is
      type T is tagged null record;
      type Local is new T with null record;
   begin
      declare
         type T is tagged null record;
         type Local is new T with null record;
      begin
         null;
      end;
   end OK;

end Local_Type_Ext;
