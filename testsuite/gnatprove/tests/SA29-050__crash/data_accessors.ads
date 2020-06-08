pragma SPARK_Mode(On);

package Data_Accessors is

generic
    Max_Length: Natural := 128;
package Bounded_Strings is

    type Bounded_String is private;

    function To_Bounded_String (S: String) return Bounded_String
    with Pre => S'Length <= Max_Length and S'Last < Natural'Last - Max_Length;
private
    subtype Bounded_String_Length_Type is Natural range 0..Max_Length;
    subtype Fixed_Length_String_Type is String (1..Max_Length);

    type Bounded_String is
        record
            Length: Bounded_String_Length_Type;
            Data: Fixed_Length_String_Type;
        end record;

    function To_Bounded_String(S: String) return Bounded_String
    is ((Length => S'Length, Data => S & (1..(Max_Length - S'Length) => ' ')));

end Bounded_Strings;

generic
    Max_Error_String_Length: Positive := 128;
package Data_Status is

    package Error_Strings is new Bounded_Strings (Max_Length => Max_Error_String_Length);

    use Error_Strings;

    type Status_Type is private;

    subtype Error_Message_Type is Error_Strings.Bounded_String;

    function Initial_Status return Status_Type;

private
    type Status_Component_Type is
        record
            Some_Field : Natural := 0;
            Error_Message : Error_Message_Type := Error_Strings.To_Bounded_String("");
        end record;

    type Status_Type is
        record
            Component     : Status_Component_Type;
        end record;

    function Initial_Status return Status_Type is (others => <>);
    -- The following results in no crash:
    -- function Initial_Status return Status_Type is (Component => (others => <>));

end Data_Status;

end Data_Accessors;
