--------------------------------------------------------------------------------
--Copyright 1998 Praxis Critical Systems Limited                              --
--                                                                            --
--The material contained herein is the subject of copyright and all rights in --
--it are reserved.  It may not be copied, in whole or in part, without the    --
--written consent of Praxis Critical Systems Limited.  Under law copying      --
-- includes translating into another language or format.                      --
--------------------------------------------------------------------------------
--                                                                            --
--Descriptor : Private child packages - mixed hierarchies
--Origin     :
--Aim        : To show that visibility rules for mixed hierarchies of public
--             and private child packages are correctly implemented
--                                                                            --
--Modification History (one line per CFR) :                                   --
--                                                                            --
--Date       CFR  Author  Checked  Details of modifications                   --
--18-Aug-98       GJF              Test added                                 --
--------------------------------------------------------------------------------

package P
is
  function F return Integer;
end P;

package Q
is
end Q;

--#inherit P, -- OK
--#        Q; -- error, not inherited by P
private package P.X
is
end P.X;

--#inherit P,    -- OK
--#        P.X;  -- error, private sibling
package P.A
is
  pragma Elaborate_Body(A);
end P.A;

package body P.A
is
  procedure Proc(I : in out Integer)
  --#derives I from I;
  is
  begin
   I := I + P.F;  -- OK
  end Proc;
end P.A;

--#inherit Q, P.A; -- both OK
package P.B
is
end P.B;

--#inherit P.X, -- OK
--#        P.A; -- error, public sibling
private package P.Y
is
end P.Y;

--#inherit P.X, P.Y, -- OK
--#        P.A,      -- error, public sibling of private parent
--#        Q;        -- error, not inherited by P
package P.X.C
is
  pragma Elaborate_Body(C);
end P.X.C;

package body P.X.C
is
  procedure Proc(I : in out Integer)
  --#derives I from I;
  is
  begin
   I := I + P.F; -- illegal call
  end Proc;
end P.X.C;

--#inherit P.X, -- OK
--#        P.A; -- error, public sibling of private parent
private package P.X.Z
is
end P.X.Z;

--#inherit P.B, -- OK
--#        P.X; -- error, private sibling of public parent
package P.A.C
is
  pragma Elaborate_Body(C);
end P.A.C;

package body P.A.C
is
  procedure Proc(I : in out Integer)
  --#derives I from I;
  is
  begin
   I := I + P.F; -- OK, call to public ancestor
  end Proc;
end P.A.C;

--#inherit P,     -- OK
--#        P.X,   -- error, private sibling of public parent
--#        P.B,   -- error, not inherited by P.A
--#        P.A.C; -- error, public sibling
private package P.A.Z
is
  pragma Elaborate_Body(Z);
end P.A.Z;

package body P.A.Z
is
  procedure Proc(I : in out Integer)
  --#derives I from I;
  is
  begin
   I := I + P.F;  -- OK, since P.A public
  end Proc;
end P.A.Z;

--#inherit P.A.C, -- OK
--#        P.A.Z; -- error, private to P.A
package P.B.C
is
end P.B.C;

--#inherit P.A.C, -- error, not inherited by P.B
--#        P.A.Z; -- error, private to P.A
private package P.B.Z
is
end P.B.Z;

--#inherit P.X.C, P.Y, -- OK
--#        P.X.Z;      -- error, private to P.X
package P.Y.C
is
end P.Y.C;

--#inherit P.X,   -- OK
--#        P.X.C, -- error, not inherited by P.Y
--#        P.X.Z, -- error, private to P.X
--#        P.Y.C; -- error, public sibling
private package P.Y.Z
is
end P.Y.Z;

with P.X, P.Y.C,   -- OK
     P.A,          -- error, public children not visible
     P.X.Z;        -- error, private to P.X;
package body P
is
  function F return Integer is separate;
end P;

--#inherit P.A, -- OK
--#        P.X; -- error, private to P
--#main_program;
procedure main
--#derives;
is
begin
  null;
end Main;
