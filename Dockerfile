FROM debian:12.10 AS builder
USER root

#  Install required software
RUN apt-get update
RUN DEBIAN_FRONTEND=noninteractive apt install -y git cmake clang

#  Build CheckMate
WORKDIR /home
#ARG branch=ng++
ARG tag=OOPSLA25

# Check out CheckMate
RUN git clone https://github.com/apre-group/checkmate --branch $tag --single-branch

# Build Z3
RUN DEBIAN_FRONTEND=noninteractive apt install -y libz3-dev


# Run example generation for examples which are not in repo
WORKDIR /home/checkmate/examples/key_examples/

COPY examples/key_examples/centipede_three.py ./
RUN python3 centipede_three.py > centipede_three.json

COPY examples/key_examples/ebos.py ./
RUN python3 ebos.py > ebos.json

COPY examples/key_examples/auction.py ./
RUN python3 auction.py > auction.json

COPY examples/key_examples/closing_game.py ./
RUN python3 closing_game.py > closing_game.json

COPY examples/key_examples/routing_game-three.py ./
RUN python3 routing_game-three.py > routing_game-three.json

COPY examples/key_examples/routing_game-unlocking.py ./
RUN python3 routing_game-unlocking.py > routing_game-unlocking.json

COPY examples/key_examples/tictactoe_convenient.py ./
RUN python3 tictactoe_convenient.py > tictactoe_convenient.json

COPY examples/key_examples/tictactoe.py ./
RUN python3 tictactoe.py > tictactoe.json


# Build CheckMate
WORKDIR /home/checkmate/
RUN cmake -B build -DCMAKE_BUILD_TYPE=Release
RUN make -C build

# Create runner container
FROM debian:12.10-slim
RUN apt-get update && apt-get install -y libz3-4
COPY --from=builder /home/checkmate/build/checkmate /usr/bin/checkmate
COPY --from=builder /home/checkmate/examples/key_examples/ /home/checkmate/examples/key_examples/
ENV PATH=$PATH:/usr/bin/
WORKDIR /home/checkmate
ENTRYPOINT [ "checkmate" ]
