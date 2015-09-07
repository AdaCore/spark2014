package body Stack with
   SPARK_Mode,
   Refined_State => (The_Stack => (Content, Top))
is
    Max : constant Natural := 100;
    type Element_Array is array (Positive range <>) of Element;
    Top : Natural := 0;
    Content : Element_Array (1 .. Max);

    procedure Pop  (E : out Element) is
    begin
       E := Content (Top);
       Top := Top - 1;
    end Pop;

    procedure Push (E : in  Element) is
    begin
       Top := Top + 1;
       Content (Top) := E;
    end Push;
end Stack;
