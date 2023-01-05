procedure Test_Simple with SPARK_Mode is

   type R is record
      F, G : Integer;
   end record with
     Predicate => F < G;

   procedure Init_Bad (I : Integer; Error : out Boolean; Value : out R) with -- @PREDICATE_CHECK:FAIL
     Relaxed_Initialization => Value,
     Post => (if not Error then Value'Initialized);

   procedure Init_Bad (I : Integer; Error : out Boolean; Value : out R) is
   begin
      if I <= 0 then
         Error := True;
         return;
      else
         Error := False;
         Value := (0, I);
      end if;
   end Init_Bad;

   type Wrapper is record
      C : R;
   end record;

   procedure Init_OK (I : Integer; Error : out Boolean; Value : out Wrapper) with -- @PREDICATE_CHECK:NONE
     Relaxed_Initialization => Value,
     Post => (if not Error then Value'Initialized);

   procedure Init_Ok (I : Integer; Error : out Boolean; Value : out Wrapper) is
   begin
      if I <= 0 then
         Error := True;
         return;
      else
         Error := False;
         Value.C := (0, I);
      end if;
   end Init_Ok;
begin
   null;
end Test_Simple;
