-- In this test the goal is to study the global variable behavior inside a callee. We also how a function call bahaves
-- if parameter permissions after the call mismatch the ones before the call. In a nutshell, we give parameters RW permissions
-- with disregard to the actual in out modes. This verification is left to the ada compiler.



with Ada.Unchecked_Deallocation;

with Ada.Text_IO;
use Ada.Text_IO;

Procedure N04 with SPARK_Mode is

  type Int_Acc is access all integer;
  type Int_Cst_Acc is access constant integer;
  var0, var1 : aliased Integer;

  Z : Int_Acc := var1'access;

  procedure Z_In (XX : in Int_Acc; YY : in out Int_Acc) with Global => (input => Z) is
  a : aliased integer := 2;
  begin
    -- XX := Z; -- Error reported here from the compiler when XX is an in parameter: assignment to "In" mode parameter not allowed
     Z.all := 2;  -- ERROR: Global parameter of mode IN.
     XX.all := 42; -- This assignment is ok even when XX is an in parameter. In fact, the in and out mode of parameters concern only the first order of the deep variable.
    -- Z := a'access; -- ERROR: non-local pointer cannot point to local object
  --  YY := Z;  -- ERROR reported for Z: expected at least "Read_Write", got "Read_Only"
    Z := YY; -- ERROR reported for Z: expected at least "Write_Only", got "Read_Only". TODO Weird: why the compiler does not complain here.
  --  XX.all := Z.all;
  --  YY := XX;
  --  XX := YY;  -- XX and YY alias. TODO we should get an error message here saying that for XX expected at least "Read_Write", got "Read_Only".
	       -- Error not shown when XX.all := 42 is run because after the assignment we give to XX (the prefix of XX.all) the RW permission.
	       -- This bug is fixed if we remove the "Set_Perm_Prefixes_Assign (N)" line 4399 (called at XX.all := 42 assignmentassigns) and which assigns Read_Write permission to assign prefixes.
    end Z_In;  --  returning X and Y permissions: RW.

  X : Int_Acc;
  Y : Int_Acc;

begin
  X := var0'access;
  -- Y := Z;   -- After the assignment Z has write_only permission. When calling test we got an error since we cannot read Z.
  Z_In (X, Y); -- XX should borrow R permissions from X; YY should borrow RW permissions from Y and then restrict them to W.
	       -- X and Y permissions become No until Z_In returns.
	       -- Before the call, X has RW permission; After the call, XX has Write_Only. ERROR generated at the procedure def site.
  Put_Line ("X = " & integer'image(X.all));  -- ERROR: We are not allowed to access X image since it alias Y. This error is not reported since we are performing an intra-procedural analysis.
					     -- X.all has permission NO effectively but seen as WR at this context (same permissions for X and Y before and after Z_In call).
end N04;
