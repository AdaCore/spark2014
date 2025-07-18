procedure Test2 with SPARK_Mode is

   --  Procedure to abruptly exit the program
   procedure Abrupt_Exit with
     Global => null,
     Always_Terminates,
     Program_Exit => True,
     Import;

   type T is new String; --  any type

   function Is_Valid (X : T) return Boolean with
     Global => null,
     Import;

   Invalid_Input : exception;

   --  Procedure which might propagate Invali_Input on invalid input
   procedure Proc (X : in out T) with
     Global => null,
     Always_Terminates,
     Exceptional_Cases => (Invalid_Input => not Is_Valid (X)'Old),
     Import;

   --  Wrapper to terminate the program in case an exception occurs
   procedure Wrap_Proc (X : in out T) with
     Global => null,
     Always_Terminates,
     Program_Exit => not Is_Valid (X)'Old;

   procedure Wrap_Proc (X : in out T) is
   begin
      Proc (X);
   exception
      when others =>
         Abrupt_Exit;
   end Wrap_Proc;

begin
   null;
end;
