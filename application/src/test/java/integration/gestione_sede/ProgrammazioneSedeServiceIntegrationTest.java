package integration.gestione_sede;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.entity.Film;
import it.unisa.application.model.entity.Proiezione;
import it.unisa.application.model.entity.Sede;
import it.unisa.application.sottosistemi.gestione_sede.service.ProgrammazioneSedeService;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import unit.test_DAO.DatabaseSetupForTest;

import java.sql.Connection;
import java.sql.Statement;
import java.time.LocalDate;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

public class ProgrammazioneSedeServiceIntegrationTest {
    private static ProgrammazioneSedeService service;

    @BeforeAll
    static void setUpDatabase() {
        DatabaseSetupForTest.configureH2DataSource();
        service = new ProgrammazioneSedeService();
    }

    private void cleanAndSeed() {
        LocalDate d1 = LocalDate.now().plusDays(3);
        LocalDate d2 = LocalDate.now().plusDays(4);

        try (Connection connection = DataSourceSingleton.getInstance().getConnection();
             Statement statement = connection.createStatement()) {

            statement.execute("SET REFERENTIAL_INTEGRITY FALSE");
            statement.execute("DELETE FROM posto_proiezione");
            statement.execute("DELETE FROM prenotazione");
            statement.execute("DELETE FROM proiezione");
            statement.execute("DELETE FROM slot");
            statement.execute("DELETE FROM sala");
            statement.execute("DELETE FROM film");
            statement.execute("DELETE FROM utente");
            statement.execute("DELETE FROM sede");
            statement.execute("SET REFERENTIAL_INTEGRITY TRUE");

            statement.execute("""
                INSERT INTO sede (id, nome, via, citta, cap) VALUES (1, 'Cinema Centrale', 'Via Roma', 'Napoli', '80100');
                INSERT INTO sala (id, id_sede, numero, capienza) VALUES (1, 1, 1, 100);
                INSERT INTO film (id, titolo, genere, classificazione, durata, descrizione, is_proiettato)
                VALUES (1, 'Avatar', 'Sci-fi', 'T', 180, 'Film di fantascienza', TRUE),
                       (2, 'Inception', 'Thriller', 'T', 148, 'Film sui sogni', TRUE);
                INSERT INTO slot (id, ora_inizio) VALUES (1, '15:00:00'), (2, '18:00:00');
            """);

            statement.execute("INSERT INTO proiezione (id, data, id_film, id_sala, id_orario) VALUES " +
                    "(1, '" + d1 + "', 1, 1, 1), " +
                    "(2, '" + d2 + "', 2, 1, 2);");

        } catch (Exception e) {
            throw new RuntimeException("Errore durante il popolamento del database di test", e);
        }
    }

    @BeforeEach
    void populateDatabase() {
        cleanAndSeed();
    }

    @Test
    void testGetProgrammazione() {
        List<Proiezione> programmazione = service.getProgrammazione(1);
        assertNotNull(programmazione);
        assertEquals(2, programmazione.size(), "La programmazione dovrebbe contenere 2 proiezioni.");
        assertTrue(programmazione.stream().anyMatch(p -> p.getFilmProiezione().getTitolo().equals("Avatar")));
    }

    @Test
    void testGetProiezioniFilm() {
        List<Proiezione> proiezioniFilm = service.getProiezioniFilm(1, 1);
        assertNotNull(proiezioniFilm);
        assertEquals(1, proiezioniFilm.size(), "Dovrebbe esserci una proiezione per il film 'Avatar'.");
        assertEquals("Avatar", proiezioniFilm.getFirst().getFilmProiezione().getTitolo());
    }

    @Test
    void testGetCatalogoSede() {
        Sede sede = new Sede(1, "Cinema Centrale", "Via Roma");
        List<Film> catalogo = service.getCatalogoSede(sede);
        assertNotNull(catalogo);
        assertEquals(2, catalogo.size());
        assertTrue(catalogo.stream().anyMatch(f -> f.getTitolo().equals("Avatar")));
        assertTrue(catalogo.stream().anyMatch(f -> f.getTitolo().equals("Inception")));
    }
}
