package integration.gestione_sede;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.sottosistemi.gestione_sede.view.ProiezioniFilmServlet;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import unit.test_DAO.DatabaseSetupForTest;

import java.lang.reflect.Method;
import java.sql.Connection;
import java.sql.Statement;
import java.time.LocalDate;

import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

public class ProiezioniFilmServletIntegrationTest {
    private ProiezioniFilmServlet servlet;
    private HttpServletRequest requestMock;
    private HttpServletResponse responseMock;
    private RequestDispatcher dispatcherMock;

    @BeforeAll
    static void setupDatabase() {
        DatabaseSetupForTest.configureH2DataSource();
    }

    private void cleanAndSeed() {
        String futureDate = LocalDate.now().plusDays(5).toString(); // YYYY-MM-DD

        try (Connection connection = DataSourceSingleton.getInstance().getConnection();
             Statement s = connection.createStatement()) {

            // pulizia tabelle (niente proiezione_slot)
            s.execute("SET REFERENTIAL_INTEGRITY FALSE");
            s.execute("DELETE FROM posto_proiezione");
            s.execute("DELETE FROM prenotazione");
            s.execute("DELETE FROM proiezione");
            s.execute("DELETE FROM slot");
            s.execute("DELETE FROM sala");
            s.execute("DELETE FROM film");
            s.execute("DELETE FROM utente");
            s.execute("DELETE FROM sede");
            s.execute("SET REFERENTIAL_INTEGRITY TRUE");

            // seed dati
            s.execute("INSERT INTO sede (id, nome, via, citta, cap) VALUES (1, 'Cinema Centrale', 'Via Roma', 'Napoli', '80100')");
            s.execute("INSERT INTO film (id, titolo, genere, classificazione, durata, descrizione, is_proiettato) " +
                    "VALUES (1, 'Avatar', 'Sci-fi', 'T', 180, 'Film di fantascienza', TRUE)");
            s.execute("INSERT INTO sala (id, id_sede, numero, capienza) VALUES (1, 1, 1, 100)");
            s.execute("INSERT INTO slot (id, ora_inizio) VALUES (1, '15:00:00')");
            s.execute("INSERT INTO proiezione (id, data, id_film, id_sala, id_orario) " +
                    "VALUES (1, '" + futureDate + "', 1, 1, 1)");
        } catch (Exception e) {
            throw new RuntimeException("Errore durante il popolamento del database di test", e);
        }
    }

    @BeforeEach
    void setUp() {
        servlet = new ProiezioniFilmServlet();
        requestMock = mock(HttpServletRequest.class);
        responseMock = mock(HttpServletResponse.class);
        dispatcherMock = mock(RequestDispatcher.class);
        cleanAndSeed();
    }

    private void invokeDoPost(HttpServletRequest request, HttpServletResponse response) throws Exception {
        Method doPost = ProiezioniFilmServlet.class.getDeclaredMethod("doPost", HttpServletRequest.class, HttpServletResponse.class);
        doPost.setAccessible(true);
        doPost.invoke(servlet, request, response);
    }

    @Test
    void testDoPostWithValidFilmAndSede() throws Exception {
        when(requestMock.getParameter("sedeId")).thenReturn("1");
        when(requestMock.getParameter("filmId")).thenReturn("1");
        when(requestMock.getRequestDispatcher("/WEB-INF/jsp/proiezioniFilm.jsp")).thenReturn(dispatcherMock);

        invokeDoPost(requestMock, responseMock);

        verify(requestMock).setAttribute(eq("programmazioneFilm"), anyList());
        verify(requestMock).setAttribute(eq("filmNome"), eq("Avatar"));
        verify(requestMock).setAttribute(eq("sedeNome"), eq("Cinema Centrale"));
        verify(dispatcherMock).forward(requestMock, responseMock);
    }

    @Test
    void testDoPostWithInvalidFilmOrSede() throws Exception {
        when(requestMock.getParameter("sedeId")).thenReturn("99");
        when(requestMock.getParameter("filmId")).thenReturn("99");
        when(requestMock.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(dispatcherMock);

        invokeDoPost(requestMock, responseMock);

        // Assumiamo che la servlet setti questo messaggio in caso di entità mancanti
        verify(requestMock).setAttribute(eq("errorMessage"), eq("Film o sede non trovati."));
        verify(dispatcherMock).forward(requestMock, responseMock);
    }

    @Test
    void testDoPostWithNoProiezioni() throws Exception {
        when(requestMock.getParameter("sedeId")).thenReturn("1");
        when(requestMock.getParameter("filmId")).thenReturn("99");
        when(requestMock.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(dispatcherMock);

        invokeDoPost(requestMock, responseMock);

        verify(requestMock).setAttribute(eq("errorMessage"), eq("Film o sede non trovati."));
        verify(dispatcherMock).forward(requestMock, responseMock);
    }

    @Test
    void testDoPostWithInvalidParameters() throws Exception {
        when(requestMock.getParameter("sedeId")).thenReturn("abc");
        when(requestMock.getParameter("filmId")).thenReturn("def");
        when(requestMock.getRequestDispatcher("/WEB-INF/jsp/error.jsp")).thenReturn(dispatcherMock);

        invokeDoPost(requestMock, responseMock);

        verify(requestMock).setAttribute(eq("errorMessage"), eq("Parametri non validi."));
        verify(dispatcherMock).forward(requestMock, responseMock);
    }
}
