with Ada.Containers;
use type Ada.Containers.Count_Type;

package body Translate with
   SPARK_Mode => On
is

    procedure Translate
       (Input : Input_T; Output : out Output_T; Success : out Boolean)
    is
    begin
        --  arbitrator translation precondition
        if Input.A > Input.B then
            --  Arbitrary translation
            Output  := (X => Input.A - 5, Y => Input.B - 5);
            Success := True;
        else
            --  Could not translate
            Output  := (X => Integer'First, Y => Integer'First);
            Success := False;
        end if;

    end Translate;

    procedure Translate
       (Input_Vector  :     Input_Vector_Package.Vector;
        Output_Vector : out Output_Vector_Package.Vector;
        Success       : out Boolean)
    is
    begin
        -- initialize output vector
        Output_Vector := Output_Vector_Package.Empty_Vector;
        Success      := True;

        for Input_Element of Input_Vector loop
            declare
                Output_Element : Output_T;
            begin
                --  translate element
                Translate (Input_Element, Output_Element, Success);

                --  if element translation succeeded, append to output vector
                if Success then
                    if Output_Vector_Package.Length (Output_Vector) < Output_Vector_Package.Last_Count then
                        Output_Vector_Package.Append
                       (Output_Vector, Output_Element);
                    else
                        Success := False;
                    end if;
                end if;
            end;
            --  break as soon as a translation fails
            exit when not Success;
        end loop;
    end Translate;

end Translate;
