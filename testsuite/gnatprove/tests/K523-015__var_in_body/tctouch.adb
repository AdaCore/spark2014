package body TCTouch is

  Collection : String (1 .. 10);
  Finger     : Natural := 0;

  procedure Touch (A_Tag : Character) is
  begin
    Finger := Finger + 1;
    Collection (Finger) := A_Tag;
  end Touch;

end TCTouch;
