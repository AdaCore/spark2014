-- Test package for adjusting Ada.Streams arrays to a fixed length
pragma SPARK_Mode;

with Ada.Streams;

package body Fixed_Stream is

    --------------------------------------------------------------------
    -- Trim_String
    -- Trim or pad one string to the length of another.
    procedure Trim_String( Change :    out String;
                           New_Val: in     String )
    is
        Len : Natural := Natural'Min( Change'Length, New_Val'Length );

    begin
        Change := (others => Character'First);

        Change(Change'First..Change'First+Integer(Len-1)) :=
          New_Val(New_Val'First..New_Val'First+Integer(Len-1));
    end Trim_String;

    --------------------------------------------------------------------
    -- Create
    -- Return a new Object with the specified character width.
    function Create( Elem_Width: in Natural;
                     Name      : in String ) return Object
    is
        This: Object;

    begin
        This.Width := Elem_Width;

        -- assign name string
        Trim_String( Change => This.Name, New_Val => Name );

        return This;
    end Create;

    --------------------------------------------------------------------
    -- Elements
    -- Return string character width.
    function Elements( This: in Object ) return Natural
    is ( This.Width );

    function Elements( This: in Object )
                      return Ada.Streams.Stream_Element_Offset
    is ( Ada.Streams.Stream_Element_Offset(This.Width) );

    --------------------------------------------------------------------
    -- Null_String
    -- Return an empty string of the correct length.
    function Null_String( This: in Object )
                         return Ada.Streams.Stream_Element_Array
    is
        Value: Ada.Streams.Stream_Element_Array
          (1..Ada.Streams.Stream_Element_Offset(This.Width)) :=
                 (others => Ada.Streams.Stream_Element'First);

    begin
        return Value;
    end Null_String;

    --------------------------------------------------------------------
    -- Convert
    -- Trim or pad provided string to the specified length.
    function Convert( This: in Object; In_String: in String )
                     return Ada.Streams.Stream_Element_Array
    is
        use Ada.Streams;
        Len       : Natural := Natural'Min( In_String'Length,
                                            This.Width );
        Out_Stream: Stream_Element_Array := This.Null_String;

    begin
        for I in 1..Integer(Len-1) loop
            Out_Stream(Out_Stream'First + Stream_Element_Offset(I)) :=
              Stream_Element(Character'Pos
                             (In_String(In_String'First + I)));
        end loop;

        return Out_Stream;
    end Convert;

end Fixed_Stream;
