# pakerat_combinators
pakerat parsing for rust proc macros using syn as cursors as the backbone

the goal is to make writing a parser thats decently performant and can do okay error messages as easy as possible.
error are desgined to be very cheap to produce and copy around so the cost of error handeling should ideally not be a major factor.

most operations are desgined to produce at least decent error messages. operations that do not usually require explicit intervention by the user to make sure the error is at least passble.


the libarary is aimed at interactive devlopment and would ideally have an assosited parser combinator that can work directly in the editor as a macro (which is much better than the usual mess that comes with these). note that because we are using syn and allowing for dynamic dispatch this can in fact be parsed in a proc_macro. more over the parser itself can be interpeted inside a proc macro and build dynamically.
