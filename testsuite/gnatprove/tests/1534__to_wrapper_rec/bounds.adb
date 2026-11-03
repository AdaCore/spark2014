procedure Bounds (Last : Positive) with SPARK_Mode is
   type RT is array (1 .. Last) of Integer;

   type Container;
   type Access_T is access Container;

   type Container is record
      Data : RT;
      Next : Access_T;
   end record;

   procedure Wibble (X : out RT; OK : out Boolean)
   with
     Relaxed_Initialization => X,
     Global                 => null,
     Always_Terminates,
     Post                   => (if OK then X'Initialized),
     Import;

   procedure Example (N : out Access_T) is
      X : RT with Relaxed_Initialization;
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
end Bounds;
