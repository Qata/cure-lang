%default total

data Reply0 = R0
data Msg = Inc | Dec | Query Reply0
data Response = Ack | Count Reply0
dispatch_bad : Msg -> Response
dispatch_bad Inc = Ack
