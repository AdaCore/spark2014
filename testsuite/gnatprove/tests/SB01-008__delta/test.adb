pragma Spark_Mode(On);

with Ada.Text_IO;

procedure Test is
    type L2_Record_Type is
        record
            L2_Field: Natural;
        end record;

    type L1_Record_Type is
        record
            L1_Field: Natural;
            L2_Record: L2_Record_Type;
        end record;

    L1: L1_Record_Type := (L2_Record => (L2_Field => 0), L1_Field => 0);

    L: L1_Record_Type := (
        L1 with delta L2_Record => (L1.L2_Record with delta L2_Field => 1)
    );
begin
    Ada.Text_IO.Put_Line("dummy text");
end Test;
