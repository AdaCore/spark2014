procedure Foo with SPARK_Mode => On is
   procedure Exit_Program with
     Import,
     Global => null,
     Always_Terminates => True,
     Exit_Cases => (True => Program_Exit),
     Ghost,
     Annotate => (GNATprove, Automatic_Instantiation);
   procedure Exit_Program_2 (F : access function return Boolean) with
     Import,
     Global => null,
     Always_Terminates => True,
     Exit_Cases => (True => Program_Exit),
     Ghost,
     Annotate => (GNATprove, Higher_Order_Specialization);
begin
   null;
end Foo;
