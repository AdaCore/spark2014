with Ada.Text_IO;
with Ada.Numerics.Discrete_Random;
with Sorting;

procedure Test_Sorting
  with SPARK_Mode => Off
is
  package Int_IO is new Ada.Text_IO.Integer_IO (Integer);

  subtype Random_Type is Integer range 0..500;
  package Int_Random is new Ada.Numerics.Discrete_Random (Random_Type);

  Gen : Int_Random.Generator;

  subtype Test_Index is Natural range 0..999;
  subtype Test_Type is Sorting.Int_Array (Test_Index);

  Test : Test_Type;
  Aux : Test_Type := Test_Type'(others => 0);

  procedure Print_Array (A : Sorting.Int_Array)
  is
  begin
    for I in Natural range A'Range
    loop
      Int_IO.Put (A (I));
      Ada.Text_IO.New_Line;
    end loop;
  end Print_Array;

  procedure Gen_Array (A : out Sorting.Int_Array)
  is
  begin
    for I in Natural range A'Range
    loop
      A (I) := Int_Random.Random (Gen);
    end loop;
  end Gen_Array;

begin
  Gen_Array (Test);

  Ada.Text_IO.Put_Line ("Unsorted:");
  Print_Array (Test);
  Ada.Text_IO.New_Line;

  Sorting.Mergesort (Test, Test'First, Test'Length, Aux);

  Ada.Text_IO.Put_Line ("Sorted:");
  Print_Array (Test);
end Test_Sorting;
