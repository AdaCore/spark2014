package body Foo
is
   type Integer_Array is array (Positive range 1 .. 100) of Integer;

   Log_In : Integer with Volatile, Async_Writers, Effective_Reads;

   Log      : Integer_Array;
   Log_Size : Natural;

   --  The depends is correct, and Get_2 works because we have a separate
   --  vertex for reading Log_In. In Get_1 we need to also do this, or
   --  somehow separate the volatiles used from the variables read (but
   --  this seems more complicated).

   procedure Get_1 with
     Global  => (In_Out => (Log, Log_Size, Log_In)),
     Depends => (Log      => (Log, Log_Size, Log_In),
                 Log_Size => Log_Size,
                 Log_In   => Log_In)
   is
   begin
      Log_Size := Log_Size + 1;
      Log (Log_Size) := Log_In;
   end Get_1;

   procedure Get_2 with
     Global  => (In_Out => (Log, Log_Size, Log_In)),
     Depends => (Log      => (Log, Log_Size, Log_In),
                 Log_Size => Log_Size,
                 Log_In   => Log_In)
   is
      Tmp : constant Integer := Log_In;
   begin
      Log_Size := Log_Size + 1;
      Log (Log_Size) := Tmp;
   end Get_2;
end Foo;
