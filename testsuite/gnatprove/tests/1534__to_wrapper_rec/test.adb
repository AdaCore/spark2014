procedure Test with SPARK_Mode is
   type RT is record
      X : Integer;
   end record;

   type Container;
   type Access_T is access Container;

   type Container is record
      Data : RT;
      Next : Access_T;
   end record;

   procedure Wibble (X : out RT; OK : out Boolean)
   with
     Relaxed_Initialization => X,
     Post                   => (if OK then X'Initialized),
     Import;

   procedure Example (N : out Access_T) is
      X  : RT
      with Relaxed_Initialization;
      OK : Boolean;
   begin
      N := null;
      loop
         Wibble (X, OK);
         exit when not OK;
         N := new Container'(Data => RT'(X), Next => N); -- @INIT_BY_PROOF:PASS
      end loop;

   end Example;
begin
   null;
end Test;
