# pakerat_combinators
pakerat parsing for rust proc macros using syn as cursors as the backbone
in terms of philosophy the goal is that it would take active dumb actions by the user to get a completly meaningless error message or no error message.


the libarary is aimed at interactive devlopment and would ideally have an assosited parser combinator that can work directly in the editor as a macro (which is much better than the usual mess that comes with these)

# TODO 
make one_of! give a mismatch instead of a message error.