procedure Foo with SPARK_Mode => On is
   procedure Exit_Program with
     Import,
     Global => null,
     Always_Terminates => True,
     Exit_Cases => (True => Program_Exit),
     Ghost,
     Annotate => (GNATprove, Automatic_Instantiation);
begin
   null;
end Foo;
